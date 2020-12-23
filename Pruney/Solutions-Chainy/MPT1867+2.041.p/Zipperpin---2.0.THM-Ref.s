%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vM4u04NsQP

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:31 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 164 expanded)
%              Number of leaves         :   26 (  64 expanded)
%              Depth                    :   14
%              Number of atoms          :  473 (1145 expanded)
%              Number of equality atoms :   23 (  40 expanded)
%              Maximal formula depth    :   19 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

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
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('2',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('11',plain,(
    k1_xboole_0 = sk_B_1 ),
    inference('sup-',[status(thm)],['1','10'])).

thf('12',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('15',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('17',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v4_pre_topc @ X17 @ X18 )
      | ~ ( v1_xboole_0 @ X17 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v4_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('21',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('24',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
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

thf('25',plain,(
    ! [X19: $i,X20: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v4_pre_topc @ X22 @ X20 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X20 ) @ X19 @ X22 )
       != ( sk_C_1 @ X19 @ X20 ) )
      | ( v2_tex_2 @ X19 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ X1 )
       != ( sk_C_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v4_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ k1_xboole_0 )
       != ( sk_C_1 @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(idempotence_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ B )
        = B ) ) )).

thf('29',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X11 @ X10 @ X10 )
        = X10 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[idempotence_k9_subset_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X1 )
      = X1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C_1 @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0
     != ( sk_C_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','31'])).

thf('33',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('36',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( r1_tarski @ ( sk_C_1 @ X19 @ X20 ) @ X19 )
      | ( v2_tex_2 @ X19 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('43',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','11'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( sk_C_1 @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('48',plain,
    ( ( sk_C_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','33','34','48'])).

thf('50',plain,(
    v2_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['12','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vM4u04NsQP
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:49:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.37/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.56  % Solved by: fo/fo7.sh
% 0.37/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.56  % done 114 iterations in 0.106s
% 0.37/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.56  % SZS output start Refutation
% 0.37/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.37/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.37/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.56  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.37/0.56  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.37/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.37/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.56  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.37/0.56  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.37/0.56  thf(t35_tex_2, conjecture,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( ( v1_xboole_0 @ B ) & 
% 0.37/0.56             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.56           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.37/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.56    (~( ![A:$i]:
% 0.37/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.37/0.56            ( l1_pre_topc @ A ) ) =>
% 0.37/0.56          ( ![B:$i]:
% 0.37/0.56            ( ( ( v1_xboole_0 @ B ) & 
% 0.37/0.56                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.56              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.37/0.56    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 0.37/0.56  thf('0', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('1', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.37/0.56  thf('2', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.56  thf(d3_tarski, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( r1_tarski @ A @ B ) <=>
% 0.37/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.37/0.56  thf('3', plain,
% 0.37/0.56      (![X4 : $i, X6 : $i]:
% 0.37/0.56         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.56  thf(d1_xboole_0, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.37/0.56  thf('4', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.37/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.37/0.56  thf('5', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['3', '4'])).
% 0.37/0.56  thf('6', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['3', '4'])).
% 0.37/0.56  thf(d10_xboole_0, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.56  thf('7', plain,
% 0.37/0.56      (![X7 : $i, X9 : $i]:
% 0.37/0.56         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.37/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.56  thf('8', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.56  thf('9', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['5', '8'])).
% 0.37/0.56  thf('10', plain,
% 0.37/0.56      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['2', '9'])).
% 0.37/0.56  thf('11', plain, (((k1_xboole_0) = (sk_B_1))),
% 0.37/0.56      inference('sup-', [status(thm)], ['1', '10'])).
% 0.37/0.56  thf('12', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.37/0.56      inference('demod', [status(thm)], ['0', '11'])).
% 0.37/0.56  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('14', plain,
% 0.37/0.56      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['2', '9'])).
% 0.37/0.56  thf(t4_subset_1, axiom,
% 0.37/0.56    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.37/0.56  thf('15', plain,
% 0.37/0.56      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 0.37/0.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.37/0.56  thf('16', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['14', '15'])).
% 0.37/0.56  thf(cc2_pre_topc, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.37/0.56  thf('17', plain,
% 0.37/0.56      (![X17 : $i, X18 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.37/0.56          | (v4_pre_topc @ X17 @ X18)
% 0.37/0.56          | ~ (v1_xboole_0 @ X17)
% 0.37/0.56          | ~ (l1_pre_topc @ X18)
% 0.37/0.56          | ~ (v2_pre_topc @ X18))),
% 0.37/0.56      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 0.37/0.56  thf('18', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (v1_xboole_0 @ X1)
% 0.37/0.56          | ~ (v2_pre_topc @ X0)
% 0.37/0.56          | ~ (l1_pre_topc @ X0)
% 0.37/0.56          | ~ (v1_xboole_0 @ X1)
% 0.37/0.56          | (v4_pre_topc @ X1 @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['16', '17'])).
% 0.37/0.56  thf('19', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((v4_pre_topc @ X1 @ X0)
% 0.37/0.56          | ~ (l1_pre_topc @ X0)
% 0.37/0.56          | ~ (v2_pre_topc @ X0)
% 0.37/0.56          | ~ (v1_xboole_0 @ X1))),
% 0.37/0.56      inference('simplify', [status(thm)], ['18'])).
% 0.37/0.56  thf('20', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (v1_xboole_0 @ X0)
% 0.37/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.37/0.56          | (v4_pre_topc @ X0 @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['13', '19'])).
% 0.37/0.56  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('22', plain,
% 0.37/0.56      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v4_pre_topc @ X0 @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['20', '21'])).
% 0.37/0.56  thf('23', plain,
% 0.37/0.56      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 0.37/0.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.37/0.56  thf('24', plain,
% 0.37/0.56      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 0.37/0.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.37/0.56  thf(d6_tex_2, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( l1_pre_topc @ A ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56           ( ( v2_tex_2 @ B @ A ) <=>
% 0.37/0.56             ( ![C:$i]:
% 0.37/0.56               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.37/0.56                      ( ![D:$i]:
% 0.37/0.56                        ( ( m1_subset_1 @
% 0.37/0.56                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.37/0.56                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.37/0.56                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.56  thf('25', plain,
% 0.37/0.56      (![X19 : $i, X20 : $i, X22 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.37/0.56          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.37/0.56          | ~ (v4_pre_topc @ X22 @ X20)
% 0.37/0.56          | ((k9_subset_1 @ (u1_struct_0 @ X20) @ X19 @ X22)
% 0.37/0.56              != (sk_C_1 @ X19 @ X20))
% 0.37/0.56          | (v2_tex_2 @ X19 @ X20)
% 0.37/0.56          | ~ (l1_pre_topc @ X20))),
% 0.37/0.56      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.37/0.56  thf('26', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (l1_pre_topc @ X0)
% 0.37/0.56          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.37/0.56          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 0.37/0.56              != (sk_C_1 @ k1_xboole_0 @ X0))
% 0.37/0.56          | ~ (v4_pre_topc @ X1 @ X0)
% 0.37/0.56          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['24', '25'])).
% 0.37/0.56  thf('27', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (v4_pre_topc @ k1_xboole_0 @ X0)
% 0.37/0.56          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ k1_xboole_0)
% 0.37/0.56              != (sk_C_1 @ k1_xboole_0 @ X0))
% 0.37/0.56          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.37/0.56          | ~ (l1_pre_topc @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['23', '26'])).
% 0.37/0.56  thf('28', plain,
% 0.37/0.56      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 0.37/0.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.37/0.56  thf(idempotence_k9_subset_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.56       ( ( k9_subset_1 @ A @ B @ B ) = ( B ) ) ))).
% 0.37/0.56  thf('29', plain,
% 0.37/0.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.56         (((k9_subset_1 @ X11 @ X10 @ X10) = (X10))
% 0.37/0.56          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 0.37/0.56      inference('cnf', [status(esa)], [idempotence_k9_subset_1])).
% 0.37/0.56  thf('30', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]: ((k9_subset_1 @ X0 @ X1 @ X1) = (X1))),
% 0.37/0.56      inference('sup-', [status(thm)], ['28', '29'])).
% 0.37/0.56  thf('31', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (v4_pre_topc @ k1_xboole_0 @ X0)
% 0.37/0.56          | ((k1_xboole_0) != (sk_C_1 @ k1_xboole_0 @ X0))
% 0.37/0.56          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.37/0.56          | ~ (l1_pre_topc @ X0))),
% 0.37/0.56      inference('demod', [status(thm)], ['27', '30'])).
% 0.37/0.56  thf('32', plain,
% 0.37/0.56      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.37/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.56        | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 0.37/0.56        | ((k1_xboole_0) != (sk_C_1 @ k1_xboole_0 @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['22', '31'])).
% 0.37/0.56  thf('33', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.56  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('35', plain,
% 0.37/0.56      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 0.37/0.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.37/0.56  thf('36', plain,
% 0.37/0.56      (![X19 : $i, X20 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.37/0.56          | (r1_tarski @ (sk_C_1 @ X19 @ X20) @ X19)
% 0.37/0.56          | (v2_tex_2 @ X19 @ X20)
% 0.37/0.56          | ~ (l1_pre_topc @ X20))),
% 0.37/0.56      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.37/0.56  thf('37', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (l1_pre_topc @ X0)
% 0.37/0.56          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.37/0.56          | (r1_tarski @ (sk_C_1 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['35', '36'])).
% 0.37/0.56  thf('38', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.56  thf('39', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.37/0.56          | ~ (l1_pre_topc @ X0)
% 0.37/0.56          | ((sk_C_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.37/0.56          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['37', '38'])).
% 0.37/0.56  thf('40', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.56  thf('41', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.37/0.56          | ~ (l1_pre_topc @ X0)
% 0.37/0.56          | ((sk_C_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.37/0.56      inference('demod', [status(thm)], ['39', '40'])).
% 0.37/0.56  thf('42', plain,
% 0.37/0.56      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['2', '9'])).
% 0.37/0.56  thf('43', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.37/0.56      inference('demod', [status(thm)], ['0', '11'])).
% 0.37/0.56  thf('44', plain,
% 0.37/0.56      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['42', '43'])).
% 0.37/0.56  thf('45', plain,
% 0.37/0.56      ((((sk_C_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))
% 0.37/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.56        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['41', '44'])).
% 0.37/0.56  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('47', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.56  thf('48', plain, (((sk_C_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.37/0.56      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.37/0.56  thf('49', plain,
% 0.37/0.56      (((v2_tex_2 @ k1_xboole_0 @ sk_A) | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.37/0.56      inference('demod', [status(thm)], ['32', '33', '34', '48'])).
% 0.37/0.56  thf('50', plain, ((v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.37/0.56      inference('simplify', [status(thm)], ['49'])).
% 0.37/0.56  thf('51', plain, ($false), inference('demod', [status(thm)], ['12', '50'])).
% 0.37/0.56  
% 0.37/0.56  % SZS output end Refutation
% 0.37/0.56  
% 0.37/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
