%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fdXuJFfTZ0

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:36 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 131 expanded)
%              Number of leaves         :   34 (  54 expanded)
%              Depth                    :   13
%              Number of atoms          :  537 ( 991 expanded)
%              Number of equality atoms :   39 (  50 expanded)
%              Maximal formula depth    :   19 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( r1_tarski @ ( sk_C @ X21 @ X22 ) @ X21 )
      | ( v2_tex_2 @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X1: $i,X3: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k4_xboole_0 @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('14',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( sk_C @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_xboole_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('20',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['16','17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','21'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('23',plain,(
    ! [X20: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X20 ) @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('24',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('25',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X10 ) @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('26',plain,(
    ! [X9: $i] :
      ( ( k2_subset_1 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('27',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('29',plain,(
    ! [X21: $i,X22: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v3_pre_topc @ X24 @ X22 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X22 ) @ X21 @ X24 )
       != ( sk_C @ X21 @ X22 ) )
      | ( v2_tex_2 @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ X1 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('32',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k9_subset_1 @ X6 @ X8 @ X7 )
        = ( k9_subset_1 @ X6 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k9_subset_1 @ X0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('35',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k9_subset_1 @ X13 @ X11 @ X12 )
        = ( k3_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('37',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k9_subset_1 @ X0 @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['33','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['30','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','44'])).

thf('46',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['18','19'])).

thf('47',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('50',plain,(
    ! [X19: $i] :
      ( ( l1_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('51',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','46','47','48','51'])).

thf('53',plain,(
    v2_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['4','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fdXuJFfTZ0
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:38:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.90/1.15  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.90/1.15  % Solved by: fo/fo7.sh
% 0.90/1.15  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.15  % done 1824 iterations in 0.701s
% 0.90/1.15  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.90/1.15  % SZS output start Refutation
% 0.90/1.15  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.90/1.15  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.90/1.15  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.90/1.15  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.90/1.15  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.90/1.15  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.15  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.15  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.90/1.15  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.90/1.15  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.90/1.15  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.90/1.15  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.15  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.90/1.15  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.90/1.15  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.90/1.15  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.90/1.15  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.90/1.15  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.90/1.15  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.90/1.15  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.90/1.15  thf(t35_tex_2, conjecture,
% 0.90/1.15    (![A:$i]:
% 0.90/1.15     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.15       ( ![B:$i]:
% 0.90/1.15         ( ( ( v1_xboole_0 @ B ) & 
% 0.90/1.15             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.90/1.15           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.90/1.15  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.15    (~( ![A:$i]:
% 0.90/1.15        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.90/1.15            ( l1_pre_topc @ A ) ) =>
% 0.90/1.15          ( ![B:$i]:
% 0.90/1.15            ( ( ( v1_xboole_0 @ B ) & 
% 0.90/1.15                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.90/1.15              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.90/1.15    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 0.90/1.15  thf('0', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.90/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.15  thf('1', plain, ((v1_xboole_0 @ sk_B)),
% 0.90/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.15  thf(l13_xboole_0, axiom,
% 0.90/1.15    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.90/1.15  thf('2', plain,
% 0.90/1.15      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.15      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.90/1.15  thf('3', plain, (((sk_B) = (k1_xboole_0))),
% 0.90/1.15      inference('sup-', [status(thm)], ['1', '2'])).
% 0.90/1.15  thf('4', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.90/1.15      inference('demod', [status(thm)], ['0', '3'])).
% 0.90/1.15  thf('5', plain,
% 0.90/1.15      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.15      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.90/1.15  thf(t4_subset_1, axiom,
% 0.90/1.15    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.90/1.15  thf('6', plain,
% 0.90/1.15      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 0.90/1.15      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.90/1.15  thf(d5_tex_2, axiom,
% 0.90/1.15    (![A:$i]:
% 0.90/1.15     ( ( l1_pre_topc @ A ) =>
% 0.90/1.15       ( ![B:$i]:
% 0.90/1.15         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.15           ( ( v2_tex_2 @ B @ A ) <=>
% 0.90/1.15             ( ![C:$i]:
% 0.90/1.15               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.15                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.90/1.15                      ( ![D:$i]:
% 0.90/1.15                        ( ( m1_subset_1 @
% 0.90/1.15                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.15                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.90/1.15                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.90/1.15                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.90/1.15  thf('7', plain,
% 0.90/1.15      (![X21 : $i, X22 : $i]:
% 0.90/1.15         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.90/1.15          | (r1_tarski @ (sk_C @ X21 @ X22) @ X21)
% 0.90/1.15          | (v2_tex_2 @ X21 @ X22)
% 0.90/1.15          | ~ (l1_pre_topc @ X22))),
% 0.90/1.15      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.90/1.15  thf('8', plain,
% 0.90/1.15      (![X0 : $i]:
% 0.90/1.15         (~ (l1_pre_topc @ X0)
% 0.90/1.15          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.90/1.15          | (r1_tarski @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.90/1.15      inference('sup-', [status(thm)], ['6', '7'])).
% 0.90/1.15  thf(l32_xboole_1, axiom,
% 0.90/1.15    (![A:$i,B:$i]:
% 0.90/1.15     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.90/1.15  thf('9', plain,
% 0.90/1.15      (![X1 : $i, X3 : $i]:
% 0.90/1.15         (((k4_xboole_0 @ X1 @ X3) = (k1_xboole_0)) | ~ (r1_tarski @ X1 @ X3))),
% 0.90/1.15      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.90/1.15  thf('10', plain,
% 0.90/1.15      (![X0 : $i]:
% 0.90/1.15         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.90/1.15          | ~ (l1_pre_topc @ X0)
% 0.90/1.15          | ((k4_xboole_0 @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.90/1.15              = (k1_xboole_0)))),
% 0.90/1.15      inference('sup-', [status(thm)], ['8', '9'])).
% 0.90/1.15  thf(t3_boole, axiom,
% 0.90/1.15    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.90/1.15  thf('11', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.90/1.15      inference('cnf', [status(esa)], [t3_boole])).
% 0.90/1.15  thf('12', plain,
% 0.90/1.15      (![X0 : $i]:
% 0.90/1.15         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.90/1.15          | ~ (l1_pre_topc @ X0)
% 0.90/1.15          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.90/1.15      inference('demod', [status(thm)], ['10', '11'])).
% 0.90/1.15  thf('13', plain,
% 0.90/1.15      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.15      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.90/1.15  thf('14', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.90/1.15      inference('demod', [status(thm)], ['0', '3'])).
% 0.90/1.15  thf('15', plain,
% 0.90/1.15      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.15      inference('sup-', [status(thm)], ['13', '14'])).
% 0.90/1.15  thf('16', plain,
% 0.90/1.15      ((((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))
% 0.90/1.15        | ~ (l1_pre_topc @ sk_A)
% 0.90/1.15        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.90/1.15      inference('sup-', [status(thm)], ['12', '15'])).
% 0.90/1.15  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.15  thf('18', plain, ((v1_xboole_0 @ sk_B)),
% 0.90/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.15  thf('19', plain, (((sk_B) = (k1_xboole_0))),
% 0.90/1.15      inference('sup-', [status(thm)], ['1', '2'])).
% 0.90/1.15  thf('20', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.90/1.15      inference('demod', [status(thm)], ['18', '19'])).
% 0.90/1.15  thf('21', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.90/1.15      inference('demod', [status(thm)], ['16', '17', '20'])).
% 0.90/1.15  thf('22', plain,
% 0.90/1.15      (![X0 : $i]:
% 0.90/1.15         (((sk_C @ X0 @ sk_A) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.15      inference('sup+', [status(thm)], ['5', '21'])).
% 0.90/1.15  thf(fc10_tops_1, axiom,
% 0.90/1.15    (![A:$i]:
% 0.90/1.15     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.15       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.90/1.15  thf('23', plain,
% 0.90/1.15      (![X20 : $i]:
% 0.90/1.15         ((v3_pre_topc @ (k2_struct_0 @ X20) @ X20)
% 0.90/1.15          | ~ (l1_pre_topc @ X20)
% 0.90/1.15          | ~ (v2_pre_topc @ X20))),
% 0.90/1.15      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.90/1.15  thf(d3_struct_0, axiom,
% 0.90/1.15    (![A:$i]:
% 0.90/1.15     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.90/1.15  thf('24', plain,
% 0.90/1.15      (![X18 : $i]:
% 0.90/1.15         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.90/1.15      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.15  thf(dt_k2_subset_1, axiom,
% 0.90/1.15    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.90/1.15  thf('25', plain,
% 0.90/1.15      (![X10 : $i]: (m1_subset_1 @ (k2_subset_1 @ X10) @ (k1_zfmisc_1 @ X10))),
% 0.90/1.15      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.90/1.15  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.90/1.15  thf('26', plain, (![X9 : $i]: ((k2_subset_1 @ X9) = (X9))),
% 0.90/1.15      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.90/1.15  thf('27', plain, (![X10 : $i]: (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X10))),
% 0.90/1.15      inference('demod', [status(thm)], ['25', '26'])).
% 0.90/1.15  thf('28', plain,
% 0.90/1.15      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 0.90/1.15      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.90/1.15  thf('29', plain,
% 0.90/1.15      (![X21 : $i, X22 : $i, X24 : $i]:
% 0.90/1.15         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.90/1.15          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.90/1.15          | ~ (v3_pre_topc @ X24 @ X22)
% 0.90/1.15          | ((k9_subset_1 @ (u1_struct_0 @ X22) @ X21 @ X24)
% 0.90/1.15              != (sk_C @ X21 @ X22))
% 0.90/1.15          | (v2_tex_2 @ X21 @ X22)
% 0.90/1.15          | ~ (l1_pre_topc @ X22))),
% 0.90/1.15      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.90/1.15  thf('30', plain,
% 0.90/1.15      (![X0 : $i, X1 : $i]:
% 0.90/1.15         (~ (l1_pre_topc @ X0)
% 0.90/1.15          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.90/1.15          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 0.90/1.15              != (sk_C @ k1_xboole_0 @ X0))
% 0.90/1.15          | ~ (v3_pre_topc @ X1 @ X0)
% 0.90/1.15          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.90/1.15      inference('sup-', [status(thm)], ['28', '29'])).
% 0.90/1.15  thf('31', plain,
% 0.90/1.15      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 0.90/1.15      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.90/1.15  thf(commutativity_k9_subset_1, axiom,
% 0.90/1.15    (![A:$i,B:$i,C:$i]:
% 0.90/1.15     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.90/1.15       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.90/1.15  thf('32', plain,
% 0.90/1.15      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.90/1.15         (((k9_subset_1 @ X6 @ X8 @ X7) = (k9_subset_1 @ X6 @ X7 @ X8))
% 0.90/1.15          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.90/1.15      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.90/1.15  thf('33', plain,
% 0.90/1.15      (![X0 : $i, X1 : $i]:
% 0.90/1.15         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.90/1.15           = (k9_subset_1 @ X0 @ k1_xboole_0 @ X1))),
% 0.90/1.15      inference('sup-', [status(thm)], ['31', '32'])).
% 0.90/1.15  thf('34', plain,
% 0.90/1.15      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 0.90/1.15      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.90/1.15  thf(redefinition_k9_subset_1, axiom,
% 0.90/1.15    (![A:$i,B:$i,C:$i]:
% 0.90/1.15     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.90/1.15       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.90/1.15  thf('35', plain,
% 0.90/1.15      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.90/1.15         (((k9_subset_1 @ X13 @ X11 @ X12) = (k3_xboole_0 @ X11 @ X12))
% 0.90/1.15          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.90/1.15      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.90/1.15  thf('36', plain,
% 0.90/1.15      (![X0 : $i, X1 : $i]:
% 0.90/1.15         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.90/1.15           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 0.90/1.15      inference('sup-', [status(thm)], ['34', '35'])).
% 0.90/1.15  thf(t2_boole, axiom,
% 0.90/1.15    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.90/1.15  thf('37', plain,
% 0.90/1.15      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.90/1.15      inference('cnf', [status(esa)], [t2_boole])).
% 0.90/1.15  thf('38', plain,
% 0.90/1.15      (![X0 : $i, X1 : $i]:
% 0.90/1.15         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.90/1.15      inference('demod', [status(thm)], ['36', '37'])).
% 0.90/1.15  thf('39', plain,
% 0.90/1.15      (![X0 : $i, X1 : $i]:
% 0.90/1.15         ((k1_xboole_0) = (k9_subset_1 @ X0 @ k1_xboole_0 @ X1))),
% 0.90/1.15      inference('demod', [status(thm)], ['33', '38'])).
% 0.90/1.15  thf('40', plain,
% 0.90/1.15      (![X0 : $i, X1 : $i]:
% 0.90/1.15         (~ (l1_pre_topc @ X0)
% 0.90/1.15          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.90/1.15          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.90/1.15          | ~ (v3_pre_topc @ X1 @ X0)
% 0.90/1.15          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.90/1.15      inference('demod', [status(thm)], ['30', '39'])).
% 0.90/1.15  thf('41', plain,
% 0.90/1.15      (![X0 : $i]:
% 0.90/1.15         (~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.90/1.15          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.90/1.15          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.90/1.15          | ~ (l1_pre_topc @ X0))),
% 0.90/1.15      inference('sup-', [status(thm)], ['27', '40'])).
% 0.90/1.15  thf('42', plain,
% 0.90/1.15      (![X0 : $i]:
% 0.90/1.15         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 0.90/1.15          | ~ (l1_struct_0 @ X0)
% 0.90/1.15          | ~ (l1_pre_topc @ X0)
% 0.90/1.15          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.90/1.15          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0)))),
% 0.90/1.15      inference('sup-', [status(thm)], ['24', '41'])).
% 0.90/1.15  thf('43', plain,
% 0.90/1.15      (![X0 : $i]:
% 0.90/1.15         (~ (v2_pre_topc @ X0)
% 0.90/1.15          | ~ (l1_pre_topc @ X0)
% 0.90/1.15          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.90/1.15          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.90/1.15          | ~ (l1_pre_topc @ X0)
% 0.90/1.15          | ~ (l1_struct_0 @ X0))),
% 0.90/1.15      inference('sup-', [status(thm)], ['23', '42'])).
% 0.90/1.15  thf('44', plain,
% 0.90/1.15      (![X0 : $i]:
% 0.90/1.15         (~ (l1_struct_0 @ X0)
% 0.90/1.15          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.90/1.15          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.90/1.15          | ~ (l1_pre_topc @ X0)
% 0.90/1.15          | ~ (v2_pre_topc @ X0))),
% 0.90/1.15      inference('simplify', [status(thm)], ['43'])).
% 0.90/1.15  thf('45', plain,
% 0.90/1.15      ((((k1_xboole_0) != (k1_xboole_0))
% 0.90/1.15        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.90/1.15        | ~ (v2_pre_topc @ sk_A)
% 0.90/1.15        | ~ (l1_pre_topc @ sk_A)
% 0.90/1.15        | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 0.90/1.15        | ~ (l1_struct_0 @ sk_A))),
% 0.90/1.15      inference('sup-', [status(thm)], ['22', '44'])).
% 0.90/1.15  thf('46', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.90/1.15      inference('demod', [status(thm)], ['18', '19'])).
% 0.90/1.15  thf('47', plain, ((v2_pre_topc @ sk_A)),
% 0.90/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.15  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.15  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.15  thf(dt_l1_pre_topc, axiom,
% 0.90/1.15    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.90/1.15  thf('50', plain,
% 0.90/1.15      (![X19 : $i]: ((l1_struct_0 @ X19) | ~ (l1_pre_topc @ X19))),
% 0.90/1.15      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.90/1.15  thf('51', plain, ((l1_struct_0 @ sk_A)),
% 0.90/1.15      inference('sup-', [status(thm)], ['49', '50'])).
% 0.90/1.15  thf('52', plain,
% 0.90/1.15      ((((k1_xboole_0) != (k1_xboole_0)) | (v2_tex_2 @ k1_xboole_0 @ sk_A))),
% 0.90/1.15      inference('demod', [status(thm)], ['45', '46', '47', '48', '51'])).
% 0.90/1.15  thf('53', plain, ((v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.90/1.15      inference('simplify', [status(thm)], ['52'])).
% 0.90/1.15  thf('54', plain, ($false), inference('demod', [status(thm)], ['4', '53'])).
% 0.90/1.15  
% 0.90/1.15  % SZS output end Refutation
% 0.90/1.15  
% 0.90/1.16  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
