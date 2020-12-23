%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OHdq6bVZaA

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:32 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 148 expanded)
%              Number of leaves         :   28 (  57 expanded)
%              Depth                    :   14
%              Number of atoms          :  481 (1068 expanded)
%              Number of equality atoms :   21 (  37 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('4',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('6',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('7',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('10',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','11'])).

thf('13',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('16',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('18',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v4_pre_topc @ X21 @ X22 )
      | ~ ( v1_xboole_0 @ X21 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v4_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('24',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('25',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
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

thf('26',plain,(
    ! [X23: $i,X24: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v4_pre_topc @ X26 @ X24 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X24 ) @ X23 @ X26 )
       != ( sk_C_1 @ X23 @ X24 ) )
      | ( v2_tex_2 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ X1 )
       != ( sk_C_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v4_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ k1_xboole_0 )
       != ( sk_C_1 @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(idempotence_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ B )
        = B ) ) )).

thf('30',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k9_subset_1 @ X9 @ X8 @ X8 )
        = X8 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[idempotence_k9_subset_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X1 )
      = X1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C_1 @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0
     != ( sk_C_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','32'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('34',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('37',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( r1_tarski @ ( sk_C_1 @ X23 @ X24 ) @ X23 )
      | ( v2_tex_2 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('42',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','12'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( sk_C_1 @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('47',plain,
    ( ( sk_C_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34','35','47'])).

thf('49',plain,(
    v2_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['13','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OHdq6bVZaA
% 0.11/0.33  % Computer   : n021.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 16:53:49 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running portfolio for 600 s
% 0.11/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.33  % Number of cores: 8
% 0.11/0.34  % Python version: Python 3.6.8
% 0.11/0.34  % Running in FO mode
% 1.06/1.27  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.06/1.27  % Solved by: fo/fo7.sh
% 1.06/1.27  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.06/1.27  % done 817 iterations in 0.830s
% 1.06/1.27  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.06/1.27  % SZS output start Refutation
% 1.06/1.27  thf(sk_B_type, type, sk_B: $i).
% 1.06/1.27  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.06/1.27  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.06/1.27  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.06/1.27  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.06/1.27  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 1.06/1.27  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.06/1.27  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.06/1.27  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.06/1.27  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 1.06/1.27  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.06/1.27  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.06/1.27  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.06/1.27  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.06/1.27  thf(sk_A_type, type, sk_A: $i).
% 1.06/1.27  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.06/1.27  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.06/1.27  thf(t35_tex_2, conjecture,
% 1.06/1.27    (![A:$i]:
% 1.06/1.27     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.27       ( ![B:$i]:
% 1.06/1.27         ( ( ( v1_xboole_0 @ B ) & 
% 1.06/1.27             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.06/1.27           ( v2_tex_2 @ B @ A ) ) ) ))).
% 1.06/1.27  thf(zf_stmt_0, negated_conjecture,
% 1.06/1.27    (~( ![A:$i]:
% 1.06/1.27        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.06/1.27            ( l1_pre_topc @ A ) ) =>
% 1.06/1.27          ( ![B:$i]:
% 1.06/1.27            ( ( ( v1_xboole_0 @ B ) & 
% 1.06/1.27                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.06/1.27              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 1.06/1.27    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 1.06/1.27  thf('0', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('1', plain, ((v1_xboole_0 @ sk_B)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf(d3_tarski, axiom,
% 1.06/1.27    (![A:$i,B:$i]:
% 1.06/1.27     ( ( r1_tarski @ A @ B ) <=>
% 1.06/1.27       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.06/1.27  thf('2', plain,
% 1.06/1.27      (![X1 : $i, X3 : $i]:
% 1.06/1.27         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.06/1.27      inference('cnf', [status(esa)], [d3_tarski])).
% 1.06/1.27  thf(d10_xboole_0, axiom,
% 1.06/1.27    (![A:$i,B:$i]:
% 1.06/1.27     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.06/1.27  thf('3', plain,
% 1.06/1.27      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 1.06/1.27      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.06/1.27  thf('4', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 1.06/1.27      inference('simplify', [status(thm)], ['3'])).
% 1.06/1.27  thf(t3_subset, axiom,
% 1.06/1.27    (![A:$i,B:$i]:
% 1.06/1.27     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.06/1.27  thf('5', plain,
% 1.06/1.27      (![X12 : $i, X14 : $i]:
% 1.06/1.27         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 1.06/1.27      inference('cnf', [status(esa)], [t3_subset])).
% 1.06/1.27  thf('6', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.06/1.27      inference('sup-', [status(thm)], ['4', '5'])).
% 1.06/1.27  thf(t5_subset, axiom,
% 1.06/1.27    (![A:$i,B:$i,C:$i]:
% 1.06/1.27     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 1.06/1.27          ( v1_xboole_0 @ C ) ) ))).
% 1.06/1.27  thf('7', plain,
% 1.06/1.27      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.06/1.27         (~ (r2_hidden @ X18 @ X19)
% 1.06/1.27          | ~ (v1_xboole_0 @ X20)
% 1.06/1.27          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 1.06/1.27      inference('cnf', [status(esa)], [t5_subset])).
% 1.06/1.27  thf('8', plain,
% 1.06/1.27      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 1.06/1.27      inference('sup-', [status(thm)], ['6', '7'])).
% 1.06/1.27  thf('9', plain,
% 1.06/1.27      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.06/1.27      inference('sup-', [status(thm)], ['2', '8'])).
% 1.06/1.27  thf(t3_xboole_1, axiom,
% 1.06/1.27    (![A:$i]:
% 1.06/1.27     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.06/1.27  thf('10', plain,
% 1.06/1.27      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ k1_xboole_0))),
% 1.06/1.27      inference('cnf', [status(esa)], [t3_xboole_1])).
% 1.06/1.27  thf('11', plain,
% 1.06/1.27      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 1.06/1.27      inference('sup-', [status(thm)], ['9', '10'])).
% 1.06/1.27  thf('12', plain, (((sk_B) = (k1_xboole_0))),
% 1.06/1.27      inference('sup-', [status(thm)], ['1', '11'])).
% 1.06/1.27  thf('13', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 1.06/1.27      inference('demod', [status(thm)], ['0', '12'])).
% 1.06/1.27  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('15', plain,
% 1.06/1.27      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.06/1.27      inference('sup-', [status(thm)], ['2', '8'])).
% 1.06/1.27  thf('16', plain,
% 1.06/1.27      (![X12 : $i, X14 : $i]:
% 1.06/1.27         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 1.06/1.27      inference('cnf', [status(esa)], [t3_subset])).
% 1.06/1.27  thf('17', plain,
% 1.06/1.27      (![X0 : $i, X1 : $i]:
% 1.06/1.27         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 1.06/1.27      inference('sup-', [status(thm)], ['15', '16'])).
% 1.06/1.27  thf(cc2_pre_topc, axiom,
% 1.06/1.27    (![A:$i]:
% 1.06/1.27     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.27       ( ![B:$i]:
% 1.06/1.27         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.27           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 1.06/1.27  thf('18', plain,
% 1.06/1.27      (![X21 : $i, X22 : $i]:
% 1.06/1.27         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.06/1.27          | (v4_pre_topc @ X21 @ X22)
% 1.06/1.27          | ~ (v1_xboole_0 @ X21)
% 1.06/1.27          | ~ (l1_pre_topc @ X22)
% 1.06/1.27          | ~ (v2_pre_topc @ X22))),
% 1.06/1.27      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 1.06/1.27  thf('19', plain,
% 1.06/1.27      (![X0 : $i, X1 : $i]:
% 1.06/1.27         (~ (v1_xboole_0 @ X1)
% 1.06/1.27          | ~ (v2_pre_topc @ X0)
% 1.06/1.27          | ~ (l1_pre_topc @ X0)
% 1.06/1.27          | ~ (v1_xboole_0 @ X1)
% 1.06/1.27          | (v4_pre_topc @ X1 @ X0))),
% 1.06/1.27      inference('sup-', [status(thm)], ['17', '18'])).
% 1.06/1.27  thf('20', plain,
% 1.06/1.27      (![X0 : $i, X1 : $i]:
% 1.06/1.27         ((v4_pre_topc @ X1 @ X0)
% 1.06/1.27          | ~ (l1_pre_topc @ X0)
% 1.06/1.27          | ~ (v2_pre_topc @ X0)
% 1.06/1.27          | ~ (v1_xboole_0 @ X1))),
% 1.06/1.27      inference('simplify', [status(thm)], ['19'])).
% 1.06/1.27  thf('21', plain,
% 1.06/1.27      (![X0 : $i]:
% 1.06/1.27         (~ (v1_xboole_0 @ X0)
% 1.06/1.27          | ~ (v2_pre_topc @ sk_A)
% 1.06/1.27          | (v4_pre_topc @ X0 @ sk_A))),
% 1.06/1.27      inference('sup-', [status(thm)], ['14', '20'])).
% 1.06/1.27  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('23', plain,
% 1.06/1.27      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v4_pre_topc @ X0 @ sk_A))),
% 1.06/1.27      inference('demod', [status(thm)], ['21', '22'])).
% 1.06/1.27  thf(t4_subset_1, axiom,
% 1.06/1.27    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.06/1.27  thf('24', plain,
% 1.06/1.27      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 1.06/1.27      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.06/1.27  thf('25', plain,
% 1.06/1.27      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 1.06/1.27      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.06/1.27  thf(d6_tex_2, axiom,
% 1.06/1.27    (![A:$i]:
% 1.06/1.27     ( ( l1_pre_topc @ A ) =>
% 1.06/1.27       ( ![B:$i]:
% 1.06/1.27         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.27           ( ( v2_tex_2 @ B @ A ) <=>
% 1.06/1.27             ( ![C:$i]:
% 1.06/1.27               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.27                 ( ~( ( r1_tarski @ C @ B ) & 
% 1.06/1.27                      ( ![D:$i]:
% 1.06/1.27                        ( ( m1_subset_1 @
% 1.06/1.27                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.27                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 1.06/1.27                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 1.06/1.27                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.06/1.27  thf('26', plain,
% 1.06/1.27      (![X23 : $i, X24 : $i, X26 : $i]:
% 1.06/1.27         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 1.06/1.27          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 1.06/1.27          | ~ (v4_pre_topc @ X26 @ X24)
% 1.06/1.27          | ((k9_subset_1 @ (u1_struct_0 @ X24) @ X23 @ X26)
% 1.06/1.27              != (sk_C_1 @ X23 @ X24))
% 1.06/1.27          | (v2_tex_2 @ X23 @ X24)
% 1.06/1.27          | ~ (l1_pre_topc @ X24))),
% 1.06/1.27      inference('cnf', [status(esa)], [d6_tex_2])).
% 1.06/1.27  thf('27', plain,
% 1.06/1.27      (![X0 : $i, X1 : $i]:
% 1.06/1.27         (~ (l1_pre_topc @ X0)
% 1.06/1.27          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 1.06/1.27          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 1.06/1.27              != (sk_C_1 @ k1_xboole_0 @ X0))
% 1.06/1.27          | ~ (v4_pre_topc @ X1 @ X0)
% 1.06/1.27          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['25', '26'])).
% 1.06/1.27  thf('28', plain,
% 1.06/1.27      (![X0 : $i]:
% 1.06/1.27         (~ (v4_pre_topc @ k1_xboole_0 @ X0)
% 1.06/1.27          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ k1_xboole_0)
% 1.06/1.27              != (sk_C_1 @ k1_xboole_0 @ X0))
% 1.06/1.27          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 1.06/1.27          | ~ (l1_pre_topc @ X0))),
% 1.06/1.27      inference('sup-', [status(thm)], ['24', '27'])).
% 1.06/1.27  thf('29', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.06/1.27      inference('sup-', [status(thm)], ['4', '5'])).
% 1.06/1.27  thf(idempotence_k9_subset_1, axiom,
% 1.06/1.27    (![A:$i,B:$i,C:$i]:
% 1.06/1.27     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.06/1.27       ( ( k9_subset_1 @ A @ B @ B ) = ( B ) ) ))).
% 1.06/1.27  thf('30', plain,
% 1.06/1.27      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.06/1.27         (((k9_subset_1 @ X9 @ X8 @ X8) = (X8))
% 1.06/1.27          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 1.06/1.27      inference('cnf', [status(esa)], [idempotence_k9_subset_1])).
% 1.06/1.27  thf('31', plain,
% 1.06/1.27      (![X0 : $i, X1 : $i]: ((k9_subset_1 @ X0 @ X1 @ X1) = (X1))),
% 1.06/1.27      inference('sup-', [status(thm)], ['29', '30'])).
% 1.06/1.27  thf('32', plain,
% 1.06/1.27      (![X0 : $i]:
% 1.06/1.27         (~ (v4_pre_topc @ k1_xboole_0 @ X0)
% 1.06/1.27          | ((k1_xboole_0) != (sk_C_1 @ k1_xboole_0 @ X0))
% 1.06/1.27          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 1.06/1.27          | ~ (l1_pre_topc @ X0))),
% 1.06/1.27      inference('demod', [status(thm)], ['28', '31'])).
% 1.06/1.27  thf('33', plain,
% 1.06/1.27      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.06/1.27        | ~ (l1_pre_topc @ sk_A)
% 1.06/1.27        | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 1.06/1.27        | ((k1_xboole_0) != (sk_C_1 @ k1_xboole_0 @ sk_A)))),
% 1.06/1.27      inference('sup-', [status(thm)], ['23', '32'])).
% 1.06/1.27  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.06/1.27  thf('34', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.06/1.27      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.06/1.27  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('36', plain,
% 1.06/1.27      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 1.06/1.27      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.06/1.27  thf('37', plain,
% 1.06/1.27      (![X23 : $i, X24 : $i]:
% 1.06/1.27         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 1.06/1.27          | (r1_tarski @ (sk_C_1 @ X23 @ X24) @ X23)
% 1.06/1.27          | (v2_tex_2 @ X23 @ X24)
% 1.06/1.27          | ~ (l1_pre_topc @ X24))),
% 1.06/1.27      inference('cnf', [status(esa)], [d6_tex_2])).
% 1.06/1.27  thf('38', plain,
% 1.06/1.27      (![X0 : $i]:
% 1.06/1.27         (~ (l1_pre_topc @ X0)
% 1.06/1.27          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 1.06/1.27          | (r1_tarski @ (sk_C_1 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 1.06/1.27      inference('sup-', [status(thm)], ['36', '37'])).
% 1.06/1.27  thf('39', plain,
% 1.06/1.27      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ k1_xboole_0))),
% 1.06/1.27      inference('cnf', [status(esa)], [t3_xboole_1])).
% 1.06/1.27  thf('40', plain,
% 1.06/1.27      (![X0 : $i]:
% 1.06/1.27         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 1.06/1.27          | ~ (l1_pre_topc @ X0)
% 1.06/1.27          | ((sk_C_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 1.06/1.27      inference('sup-', [status(thm)], ['38', '39'])).
% 1.06/1.27  thf('41', plain,
% 1.06/1.27      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 1.06/1.27      inference('sup-', [status(thm)], ['9', '10'])).
% 1.06/1.27  thf('42', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 1.06/1.27      inference('demod', [status(thm)], ['0', '12'])).
% 1.06/1.27  thf('43', plain,
% 1.06/1.27      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 1.06/1.27      inference('sup-', [status(thm)], ['41', '42'])).
% 1.06/1.27  thf('44', plain,
% 1.06/1.27      ((((sk_C_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))
% 1.06/1.27        | ~ (l1_pre_topc @ sk_A)
% 1.06/1.27        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.06/1.27      inference('sup-', [status(thm)], ['40', '43'])).
% 1.06/1.27  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('46', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.06/1.27      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.06/1.27  thf('47', plain, (((sk_C_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 1.06/1.27      inference('demod', [status(thm)], ['44', '45', '46'])).
% 1.06/1.27  thf('48', plain,
% 1.06/1.27      (((v2_tex_2 @ k1_xboole_0 @ sk_A) | ((k1_xboole_0) != (k1_xboole_0)))),
% 1.06/1.27      inference('demod', [status(thm)], ['33', '34', '35', '47'])).
% 1.06/1.27  thf('49', plain, ((v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 1.06/1.27      inference('simplify', [status(thm)], ['48'])).
% 1.06/1.27  thf('50', plain, ($false), inference('demod', [status(thm)], ['13', '49'])).
% 1.06/1.27  
% 1.06/1.27  % SZS output end Refutation
% 1.06/1.27  
% 1.06/1.28  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
