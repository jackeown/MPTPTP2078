%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.C4T0kTKYUo

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:03 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 116 expanded)
%              Number of leaves         :   31 (  48 expanded)
%              Depth                    :   21
%              Number of atoms          :  495 (1536 expanded)
%              Number of equality atoms :    8 (  37 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ X7 ) ) ),
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
    ! [X14: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X14 ) @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('5',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc4_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('6',plain,(
    ! [X12: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X12 ) @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc4_pre_topc])).

thf('7',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('8',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X3 ) @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('9',plain,(
    ! [X2: $i] :
      ( ( k2_subset_1 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('10',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X15: $i] :
      ( ~ ( v3_pre_topc @ X15 @ sk_A )
      | ~ ( v4_pre_topc @ X15 @ sk_A )
      | ~ ( r2_hidden @ sk_B_1 @ X15 )
      | ( r2_hidden @ X15 @ sk_C )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X15: $i] :
      ( ~ ( v3_pre_topc @ X15 @ sk_A )
      | ~ ( v4_pre_topc @ X15 @ sk_A )
      | ~ ( r2_hidden @ sk_B_1 @ X15 )
      | ( r2_hidden @ X15 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('17',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('18',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['6','19'])).

thf('21',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','23'])).

thf('25',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('26',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','26'])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','30'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('32',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_tarski @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('34',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('35',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(rc7_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('36',plain,(
    ! [X13: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('37',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_xboole_0 @ ( sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X13: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B @ X13 ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['0','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.C4T0kTKYUo
% 0.16/0.37  % Computer   : n016.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 17:56:04 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.35/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.53  % Solved by: fo/fo7.sh
% 0.35/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.53  % done 104 iterations in 0.045s
% 0.35/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.53  % SZS output start Refutation
% 0.35/0.53  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.35/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.35/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.35/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.35/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.35/0.53  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.35/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.53  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.35/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.35/0.53  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.35/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.35/0.53  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.35/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.35/0.53  thf(t28_connsp_2, conjecture,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.53       ( ![B:$i]:
% 0.35/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.53           ( ![C:$i]:
% 0.35/0.53             ( ( m1_subset_1 @
% 0.35/0.53                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.35/0.53               ( ~( ( ![D:$i]:
% 0.35/0.53                      ( ( m1_subset_1 @
% 0.35/0.53                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.53                        ( ( r2_hidden @ D @ C ) <=>
% 0.35/0.53                          ( ( v3_pre_topc @ D @ A ) & 
% 0.35/0.53                            ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.35/0.53                    ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.35/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.53    (~( ![A:$i]:
% 0.35/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.35/0.53            ( l1_pre_topc @ A ) ) =>
% 0.35/0.53          ( ![B:$i]:
% 0.35/0.53            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.53              ( ![C:$i]:
% 0.35/0.53                ( ( m1_subset_1 @
% 0.35/0.53                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.35/0.53                  ( ~( ( ![D:$i]:
% 0.35/0.53                         ( ( m1_subset_1 @
% 0.35/0.53                             D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.53                           ( ( r2_hidden @ D @ C ) <=>
% 0.35/0.53                             ( ( v3_pre_topc @ D @ A ) & 
% 0.35/0.53                               ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.35/0.53                       ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.35/0.53    inference('cnf.neg', [status(esa)], [t28_connsp_2])).
% 0.35/0.53  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('1', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(t2_subset, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( m1_subset_1 @ A @ B ) =>
% 0.35/0.53       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.35/0.53  thf('2', plain,
% 0.35/0.53      (![X6 : $i, X7 : $i]:
% 0.35/0.53         ((r2_hidden @ X6 @ X7)
% 0.35/0.53          | (v1_xboole_0 @ X7)
% 0.35/0.53          | ~ (m1_subset_1 @ X6 @ X7))),
% 0.35/0.53      inference('cnf', [status(esa)], [t2_subset])).
% 0.35/0.53  thf('3', plain,
% 0.35/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.53        | (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.35/0.53  thf(fc10_tops_1, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.53       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.35/0.53  thf('4', plain,
% 0.35/0.53      (![X14 : $i]:
% 0.35/0.53         ((v3_pre_topc @ (k2_struct_0 @ X14) @ X14)
% 0.35/0.53          | ~ (l1_pre_topc @ X14)
% 0.35/0.53          | ~ (v2_pre_topc @ X14))),
% 0.35/0.53      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.35/0.53  thf(d3_struct_0, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.35/0.53  thf('5', plain,
% 0.35/0.53      (![X10 : $i]:
% 0.35/0.53         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 0.35/0.53      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.35/0.53  thf(fc4_pre_topc, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.53       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.35/0.53  thf('6', plain,
% 0.35/0.53      (![X12 : $i]:
% 0.35/0.53         ((v4_pre_topc @ (k2_struct_0 @ X12) @ X12)
% 0.35/0.53          | ~ (l1_pre_topc @ X12)
% 0.35/0.53          | ~ (v2_pre_topc @ X12))),
% 0.35/0.53      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.35/0.53  thf('7', plain,
% 0.35/0.53      (![X10 : $i]:
% 0.35/0.53         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 0.35/0.53      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.35/0.53  thf(dt_k2_subset_1, axiom,
% 0.35/0.53    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.35/0.53  thf('8', plain,
% 0.35/0.53      (![X3 : $i]: (m1_subset_1 @ (k2_subset_1 @ X3) @ (k1_zfmisc_1 @ X3))),
% 0.35/0.53      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.35/0.53  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.35/0.53  thf('9', plain, (![X2 : $i]: ((k2_subset_1 @ X2) = (X2))),
% 0.35/0.53      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.35/0.53  thf('10', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.35/0.53      inference('demod', [status(thm)], ['8', '9'])).
% 0.35/0.53  thf('11', plain,
% 0.35/0.53      (![X15 : $i]:
% 0.35/0.53         (~ (v3_pre_topc @ X15 @ sk_A)
% 0.35/0.53          | ~ (v4_pre_topc @ X15 @ sk_A)
% 0.35/0.53          | ~ (r2_hidden @ sk_B_1 @ X15)
% 0.35/0.53          | (r2_hidden @ X15 @ sk_C)
% 0.35/0.53          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('12', plain, (((sk_C) = (k1_xboole_0))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('13', plain,
% 0.35/0.53      (![X15 : $i]:
% 0.35/0.53         (~ (v3_pre_topc @ X15 @ sk_A)
% 0.35/0.53          | ~ (v4_pre_topc @ X15 @ sk_A)
% 0.35/0.53          | ~ (r2_hidden @ sk_B_1 @ X15)
% 0.35/0.53          | (r2_hidden @ X15 @ k1_xboole_0)
% 0.35/0.53          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.35/0.53      inference('demod', [status(thm)], ['11', '12'])).
% 0.35/0.53  thf('14', plain,
% 0.35/0.53      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.35/0.53        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.35/0.53        | ~ (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.35/0.53        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.35/0.53      inference('sup-', [status(thm)], ['10', '13'])).
% 0.35/0.53  thf('15', plain,
% 0.35/0.53      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.35/0.53        | ~ (l1_struct_0 @ sk_A)
% 0.35/0.53        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.35/0.53        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.35/0.53        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['7', '14'])).
% 0.35/0.53  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(dt_l1_pre_topc, axiom,
% 0.35/0.53    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.35/0.53  thf('17', plain,
% 0.35/0.53      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.35/0.53      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.35/0.53  thf('18', plain, ((l1_struct_0 @ sk_A)),
% 0.35/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.35/0.53  thf('19', plain,
% 0.35/0.53      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.35/0.53        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.35/0.53        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.35/0.53        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.35/0.53      inference('demod', [status(thm)], ['15', '18'])).
% 0.35/0.53  thf('20', plain,
% 0.35/0.53      ((~ (v2_pre_topc @ sk_A)
% 0.35/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.35/0.53        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.35/0.53        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.35/0.53        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.35/0.53      inference('sup-', [status(thm)], ['6', '19'])).
% 0.35/0.53  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('23', plain,
% 0.35/0.53      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.35/0.53        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.35/0.53        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.35/0.53      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.35/0.53  thf('24', plain,
% 0.35/0.53      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.35/0.53        | ~ (l1_struct_0 @ sk_A)
% 0.35/0.53        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.35/0.53        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['5', '23'])).
% 0.35/0.53  thf('25', plain, ((l1_struct_0 @ sk_A)),
% 0.35/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.35/0.53  thf('26', plain,
% 0.35/0.53      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.35/0.53        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.35/0.53        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.35/0.53      inference('demod', [status(thm)], ['24', '25'])).
% 0.35/0.53  thf('27', plain,
% 0.35/0.53      ((~ (v2_pre_topc @ sk_A)
% 0.35/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.35/0.53        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.35/0.53        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['4', '26'])).
% 0.35/0.53  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('30', plain,
% 0.35/0.53      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.35/0.53        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.35/0.53  thf('31', plain,
% 0.35/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.53        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['3', '30'])).
% 0.35/0.53  thf(t7_ordinal1, axiom,
% 0.35/0.53    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.35/0.53  thf('32', plain,
% 0.35/0.53      (![X8 : $i, X9 : $i]: (~ (r2_hidden @ X8 @ X9) | ~ (r1_tarski @ X9 @ X8))),
% 0.35/0.53      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.35/0.53  thf('33', plain,
% 0.35/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.53        | ~ (r1_tarski @ k1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['31', '32'])).
% 0.35/0.53  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.35/0.53  thf('34', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.35/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.35/0.53  thf('35', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.35/0.53      inference('demod', [status(thm)], ['33', '34'])).
% 0.35/0.53  thf(rc7_pre_topc, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.53       ( ?[B:$i]:
% 0.35/0.53         ( ( v4_pre_topc @ B @ A ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.35/0.53           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.35/0.53  thf('36', plain,
% 0.35/0.53      (![X13 : $i]:
% 0.35/0.53         ((m1_subset_1 @ (sk_B @ X13) @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.35/0.53          | ~ (l1_pre_topc @ X13)
% 0.35/0.53          | ~ (v2_pre_topc @ X13)
% 0.35/0.53          | (v2_struct_0 @ X13))),
% 0.35/0.53      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.35/0.53  thf(cc1_subset_1, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( v1_xboole_0 @ A ) =>
% 0.35/0.53       ( ![B:$i]:
% 0.35/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.35/0.53  thf('37', plain,
% 0.35/0.53      (![X4 : $i, X5 : $i]:
% 0.35/0.53         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.35/0.53          | (v1_xboole_0 @ X4)
% 0.35/0.53          | ~ (v1_xboole_0 @ X5))),
% 0.35/0.53      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.35/0.53  thf('38', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((v2_struct_0 @ X0)
% 0.35/0.53          | ~ (v2_pre_topc @ X0)
% 0.35/0.53          | ~ (l1_pre_topc @ X0)
% 0.35/0.53          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.35/0.53          | (v1_xboole_0 @ (sk_B @ X0)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['36', '37'])).
% 0.35/0.53  thf('39', plain,
% 0.35/0.53      (((v1_xboole_0 @ (sk_B @ sk_A))
% 0.35/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.35/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.35/0.53        | (v2_struct_0 @ sk_A))),
% 0.35/0.53      inference('sup-', [status(thm)], ['35', '38'])).
% 0.35/0.53  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('42', plain, (((v1_xboole_0 @ (sk_B @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.35/0.53      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.35/0.53  thf('43', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('44', plain, ((v1_xboole_0 @ (sk_B @ sk_A))),
% 0.35/0.53      inference('clc', [status(thm)], ['42', '43'])).
% 0.35/0.53  thf('45', plain,
% 0.35/0.53      (![X13 : $i]:
% 0.35/0.53         (~ (v1_xboole_0 @ (sk_B @ X13))
% 0.35/0.53          | ~ (l1_pre_topc @ X13)
% 0.35/0.53          | ~ (v2_pre_topc @ X13)
% 0.35/0.53          | (v2_struct_0 @ X13))),
% 0.35/0.53      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.35/0.53  thf('46', plain,
% 0.35/0.53      (((v2_struct_0 @ sk_A) | ~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 0.35/0.53      inference('sup-', [status(thm)], ['44', '45'])).
% 0.35/0.53  thf('47', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('49', plain, ((v2_struct_0 @ sk_A)),
% 0.35/0.53      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.35/0.53  thf('50', plain, ($false), inference('demod', [status(thm)], ['0', '49'])).
% 0.35/0.53  
% 0.35/0.53  % SZS output end Refutation
% 0.35/0.53  
% 0.39/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
