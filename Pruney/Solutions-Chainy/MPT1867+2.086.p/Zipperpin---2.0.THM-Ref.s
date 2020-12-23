%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xhumWW89PO

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:38 EST 2020

% Result     : Theorem 0.66s
% Output     : Refutation 0.66s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 130 expanded)
%              Number of leaves         :   33 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :  495 ( 965 expanded)
%              Number of equality atoms :   34 (  48 expanded)
%              Maximal formula depth    :   19 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

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
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('6',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
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

thf('7',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( r1_tarski @ ( sk_C @ X18 @ X19 ) @ X18 )
      | ( v2_tex_2 @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('12',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( sk_C @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_xboole_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('18',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['14','15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','19'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('21',plain,(
    ! [X17: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X17 ) @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('22',plain,(
    ! [X15: $i] :
      ( ( ( k2_struct_0 @ X15 )
        = ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('23',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X7 ) @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('24',plain,(
    ! [X6: $i] :
      ( ( k2_subset_1 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('25',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('27',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v3_pre_topc @ X21 @ X19 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X19 ) @ X18 @ X21 )
       != ( sk_C @ X18 @ X19 ) )
      | ( v2_tex_2 @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ X1 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ ( u1_struct_0 @ X0 ) )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('31',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k9_subset_1 @ X10 @ X8 @ X9 )
        = ( k3_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('33',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('34',plain,(
    ! [X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X2 ) @ X1 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('35',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['29','32','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','41'])).

thf('43',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['16','17'])).

thf('44',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('47',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('48',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['42','43','44','45','48'])).

thf('50',plain,(
    v2_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['4','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xhumWW89PO
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:19:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.66/0.84  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.66/0.84  % Solved by: fo/fo7.sh
% 0.66/0.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.66/0.84  % done 779 iterations in 0.393s
% 0.66/0.84  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.66/0.84  % SZS output start Refutation
% 0.66/0.84  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.66/0.84  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.66/0.84  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.66/0.84  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.66/0.84  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.66/0.84  thf(sk_B_type, type, sk_B: $i).
% 0.66/0.84  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.66/0.84  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.66/0.84  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.66/0.84  thf(sk_A_type, type, sk_A: $i).
% 0.66/0.84  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.66/0.84  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.66/0.84  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.66/0.84  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.66/0.84  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.66/0.84  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.66/0.84  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.66/0.84  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.66/0.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.66/0.84  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.66/0.84  thf(t35_tex_2, conjecture,
% 0.66/0.84    (![A:$i]:
% 0.66/0.84     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.66/0.84       ( ![B:$i]:
% 0.66/0.84         ( ( ( v1_xboole_0 @ B ) & 
% 0.66/0.84             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.66/0.84           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.66/0.84  thf(zf_stmt_0, negated_conjecture,
% 0.66/0.84    (~( ![A:$i]:
% 0.66/0.84        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.66/0.84            ( l1_pre_topc @ A ) ) =>
% 0.66/0.84          ( ![B:$i]:
% 0.66/0.84            ( ( ( v1_xboole_0 @ B ) & 
% 0.66/0.84                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.66/0.84              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.66/0.84    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 0.66/0.84  thf('0', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('1', plain, ((v1_xboole_0 @ sk_B)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf(l13_xboole_0, axiom,
% 0.66/0.84    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.66/0.84  thf('2', plain,
% 0.66/0.84      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.66/0.84      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.66/0.84  thf('3', plain, (((sk_B) = (k1_xboole_0))),
% 0.66/0.84      inference('sup-', [status(thm)], ['1', '2'])).
% 0.66/0.84  thf('4', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.66/0.84      inference('demod', [status(thm)], ['0', '3'])).
% 0.66/0.84  thf('5', plain,
% 0.66/0.84      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.66/0.84      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.66/0.84  thf(t4_subset_1, axiom,
% 0.66/0.84    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.66/0.84  thf('6', plain,
% 0.66/0.84      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.66/0.84      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.66/0.84  thf(d5_tex_2, axiom,
% 0.66/0.84    (![A:$i]:
% 0.66/0.84     ( ( l1_pre_topc @ A ) =>
% 0.66/0.84       ( ![B:$i]:
% 0.66/0.84         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.66/0.84           ( ( v2_tex_2 @ B @ A ) <=>
% 0.66/0.84             ( ![C:$i]:
% 0.66/0.84               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.66/0.84                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.66/0.84                      ( ![D:$i]:
% 0.66/0.84                        ( ( m1_subset_1 @
% 0.66/0.84                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.66/0.84                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.66/0.84                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.66/0.84                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.66/0.84  thf('7', plain,
% 0.66/0.84      (![X18 : $i, X19 : $i]:
% 0.66/0.84         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.66/0.84          | (r1_tarski @ (sk_C @ X18 @ X19) @ X18)
% 0.66/0.84          | (v2_tex_2 @ X18 @ X19)
% 0.66/0.84          | ~ (l1_pre_topc @ X19))),
% 0.66/0.84      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.66/0.84  thf('8', plain,
% 0.66/0.84      (![X0 : $i]:
% 0.66/0.84         (~ (l1_pre_topc @ X0)
% 0.66/0.84          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.66/0.84          | (r1_tarski @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.66/0.84      inference('sup-', [status(thm)], ['6', '7'])).
% 0.66/0.84  thf(t3_xboole_1, axiom,
% 0.66/0.84    (![A:$i]:
% 0.66/0.84     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.66/0.84  thf('9', plain,
% 0.66/0.84      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 0.66/0.84      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.66/0.84  thf('10', plain,
% 0.66/0.84      (![X0 : $i]:
% 0.66/0.84         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.66/0.84          | ~ (l1_pre_topc @ X0)
% 0.66/0.84          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.66/0.84      inference('sup-', [status(thm)], ['8', '9'])).
% 0.66/0.84  thf('11', plain,
% 0.66/0.84      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.66/0.84      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.66/0.84  thf('12', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.66/0.84      inference('demod', [status(thm)], ['0', '3'])).
% 0.66/0.84  thf('13', plain,
% 0.66/0.84      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.66/0.84      inference('sup-', [status(thm)], ['11', '12'])).
% 0.66/0.84  thf('14', plain,
% 0.66/0.84      ((((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))
% 0.66/0.84        | ~ (l1_pre_topc @ sk_A)
% 0.66/0.84        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.66/0.84      inference('sup-', [status(thm)], ['10', '13'])).
% 0.66/0.84  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('16', plain, ((v1_xboole_0 @ sk_B)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('17', plain, (((sk_B) = (k1_xboole_0))),
% 0.66/0.84      inference('sup-', [status(thm)], ['1', '2'])).
% 0.66/0.84  thf('18', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.66/0.84      inference('demod', [status(thm)], ['16', '17'])).
% 0.66/0.84  thf('19', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.66/0.84      inference('demod', [status(thm)], ['14', '15', '18'])).
% 0.66/0.84  thf('20', plain,
% 0.66/0.84      (![X0 : $i]:
% 0.66/0.84         (((sk_C @ X0 @ sk_A) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.66/0.84      inference('sup+', [status(thm)], ['5', '19'])).
% 0.66/0.84  thf(fc10_tops_1, axiom,
% 0.66/0.84    (![A:$i]:
% 0.66/0.84     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.66/0.84       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.66/0.84  thf('21', plain,
% 0.66/0.84      (![X17 : $i]:
% 0.66/0.84         ((v3_pre_topc @ (k2_struct_0 @ X17) @ X17)
% 0.66/0.84          | ~ (l1_pre_topc @ X17)
% 0.66/0.84          | ~ (v2_pre_topc @ X17))),
% 0.66/0.84      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.66/0.84  thf(d3_struct_0, axiom,
% 0.66/0.84    (![A:$i]:
% 0.66/0.84     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.66/0.84  thf('22', plain,
% 0.66/0.84      (![X15 : $i]:
% 0.66/0.84         (((k2_struct_0 @ X15) = (u1_struct_0 @ X15)) | ~ (l1_struct_0 @ X15))),
% 0.66/0.84      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.66/0.84  thf(dt_k2_subset_1, axiom,
% 0.66/0.84    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.66/0.84  thf('23', plain,
% 0.66/0.84      (![X7 : $i]: (m1_subset_1 @ (k2_subset_1 @ X7) @ (k1_zfmisc_1 @ X7))),
% 0.66/0.84      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.66/0.84  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.66/0.84  thf('24', plain, (![X6 : $i]: ((k2_subset_1 @ X6) = (X6))),
% 0.66/0.84      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.66/0.84  thf('25', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 0.66/0.84      inference('demod', [status(thm)], ['23', '24'])).
% 0.66/0.84  thf('26', plain,
% 0.66/0.84      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.66/0.84      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.66/0.84  thf('27', plain,
% 0.66/0.84      (![X18 : $i, X19 : $i, X21 : $i]:
% 0.66/0.84         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.66/0.84          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.66/0.84          | ~ (v3_pre_topc @ X21 @ X19)
% 0.66/0.84          | ((k9_subset_1 @ (u1_struct_0 @ X19) @ X18 @ X21)
% 0.66/0.84              != (sk_C @ X18 @ X19))
% 0.66/0.84          | (v2_tex_2 @ X18 @ X19)
% 0.66/0.84          | ~ (l1_pre_topc @ X19))),
% 0.66/0.84      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.66/0.84  thf('28', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         (~ (l1_pre_topc @ X0)
% 0.66/0.84          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.66/0.84          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 0.66/0.84              != (sk_C @ k1_xboole_0 @ X0))
% 0.66/0.84          | ~ (v3_pre_topc @ X1 @ X0)
% 0.66/0.84          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.66/0.84      inference('sup-', [status(thm)], ['26', '27'])).
% 0.66/0.84  thf('29', plain,
% 0.66/0.84      (![X0 : $i]:
% 0.66/0.84         (~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.66/0.84          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ 
% 0.66/0.84              (u1_struct_0 @ X0)) != (sk_C @ k1_xboole_0 @ X0))
% 0.66/0.84          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.66/0.84          | ~ (l1_pre_topc @ X0))),
% 0.66/0.84      inference('sup-', [status(thm)], ['25', '28'])).
% 0.66/0.84  thf('30', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 0.66/0.84      inference('demod', [status(thm)], ['23', '24'])).
% 0.66/0.84  thf(redefinition_k9_subset_1, axiom,
% 0.66/0.84    (![A:$i,B:$i,C:$i]:
% 0.66/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.66/0.84       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.66/0.84  thf('31', plain,
% 0.66/0.84      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.66/0.84         (((k9_subset_1 @ X10 @ X8 @ X9) = (k3_xboole_0 @ X8 @ X9))
% 0.66/0.84          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.66/0.84      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.66/0.84  thf('32', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.66/0.84      inference('sup-', [status(thm)], ['30', '31'])).
% 0.66/0.84  thf(t48_xboole_1, axiom,
% 0.66/0.84    (![A:$i,B:$i]:
% 0.66/0.84     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.66/0.84  thf('33', plain,
% 0.66/0.84      (![X4 : $i, X5 : $i]:
% 0.66/0.84         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X4 @ X5))
% 0.66/0.84           = (k3_xboole_0 @ X4 @ X5))),
% 0.66/0.84      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.66/0.84  thf(t36_xboole_1, axiom,
% 0.66/0.84    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.66/0.84  thf('34', plain,
% 0.66/0.84      (![X1 : $i, X2 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X2) @ X1)),
% 0.66/0.84      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.66/0.84  thf('35', plain,
% 0.66/0.84      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 0.66/0.84      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.66/0.84  thf('36', plain,
% 0.66/0.84      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.66/0.84      inference('sup-', [status(thm)], ['34', '35'])).
% 0.66/0.84  thf('37', plain,
% 0.66/0.84      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.66/0.84      inference('sup+', [status(thm)], ['33', '36'])).
% 0.66/0.84  thf('38', plain,
% 0.66/0.84      (![X0 : $i]:
% 0.66/0.84         (~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.66/0.84          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.66/0.84          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.66/0.84          | ~ (l1_pre_topc @ X0))),
% 0.66/0.84      inference('demod', [status(thm)], ['29', '32', '37'])).
% 0.66/0.84  thf('39', plain,
% 0.66/0.84      (![X0 : $i]:
% 0.66/0.84         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 0.66/0.84          | ~ (l1_struct_0 @ X0)
% 0.66/0.84          | ~ (l1_pre_topc @ X0)
% 0.66/0.84          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.66/0.84          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0)))),
% 0.66/0.84      inference('sup-', [status(thm)], ['22', '38'])).
% 0.66/0.84  thf('40', plain,
% 0.66/0.84      (![X0 : $i]:
% 0.66/0.84         (~ (v2_pre_topc @ X0)
% 0.66/0.84          | ~ (l1_pre_topc @ X0)
% 0.66/0.84          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.66/0.84          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.66/0.84          | ~ (l1_pre_topc @ X0)
% 0.66/0.84          | ~ (l1_struct_0 @ X0))),
% 0.66/0.84      inference('sup-', [status(thm)], ['21', '39'])).
% 0.66/0.84  thf('41', plain,
% 0.66/0.84      (![X0 : $i]:
% 0.66/0.84         (~ (l1_struct_0 @ X0)
% 0.66/0.84          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.66/0.84          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.66/0.84          | ~ (l1_pre_topc @ X0)
% 0.66/0.84          | ~ (v2_pre_topc @ X0))),
% 0.66/0.84      inference('simplify', [status(thm)], ['40'])).
% 0.66/0.84  thf('42', plain,
% 0.66/0.84      ((((k1_xboole_0) != (k1_xboole_0))
% 0.66/0.84        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.66/0.84        | ~ (v2_pre_topc @ sk_A)
% 0.66/0.84        | ~ (l1_pre_topc @ sk_A)
% 0.66/0.84        | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 0.66/0.84        | ~ (l1_struct_0 @ sk_A))),
% 0.66/0.84      inference('sup-', [status(thm)], ['20', '41'])).
% 0.66/0.84  thf('43', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.66/0.84      inference('demod', [status(thm)], ['16', '17'])).
% 0.66/0.84  thf('44', plain, ((v2_pre_topc @ sk_A)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf(dt_l1_pre_topc, axiom,
% 0.66/0.84    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.66/0.84  thf('47', plain,
% 0.66/0.84      (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_pre_topc @ X16))),
% 0.66/0.84      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.66/0.84  thf('48', plain, ((l1_struct_0 @ sk_A)),
% 0.66/0.84      inference('sup-', [status(thm)], ['46', '47'])).
% 0.66/0.84  thf('49', plain,
% 0.66/0.84      ((((k1_xboole_0) != (k1_xboole_0)) | (v2_tex_2 @ k1_xboole_0 @ sk_A))),
% 0.66/0.84      inference('demod', [status(thm)], ['42', '43', '44', '45', '48'])).
% 0.66/0.84  thf('50', plain, ((v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.66/0.84      inference('simplify', [status(thm)], ['49'])).
% 0.66/0.84  thf('51', plain, ($false), inference('demod', [status(thm)], ['4', '50'])).
% 0.66/0.84  
% 0.66/0.84  % SZS output end Refutation
% 0.66/0.84  
% 0.66/0.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
