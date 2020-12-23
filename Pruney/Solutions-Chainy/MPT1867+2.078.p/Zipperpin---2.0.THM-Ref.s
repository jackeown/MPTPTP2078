%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Xs48DfqzX3

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:36 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
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

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( r1_tarski @ ( sk_C @ X20 @ X21 ) @ X20 )
      | ( v2_tex_2 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('9',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_xboole_0 @ X2 @ X1 )
        = X1 )
      | ~ ( r1_tarski @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_xboole_0 @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

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
    ! [X19: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X19 ) @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('24',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('25',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X9 ) @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('26',plain,(
    ! [X8: $i] :
      ( ( k2_subset_1 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('27',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('29',plain,(
    ! [X20: $i,X21: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_pre_topc @ X23 @ X21 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X21 ) @ X20 @ X23 )
       != ( sk_C @ X20 @ X21 ) )
      | ( v2_tex_2 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
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
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('32',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k9_subset_1 @ X5 @ X7 @ X6 )
        = ( k9_subset_1 @ X5 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k9_subset_1 @ X0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('35',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X12 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
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
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
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
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Xs48DfqzX3
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:49:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.60/0.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.60/0.77  % Solved by: fo/fo7.sh
% 0.60/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.77  % done 760 iterations in 0.316s
% 0.60/0.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.60/0.77  % SZS output start Refutation
% 0.60/0.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.60/0.77  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.60/0.77  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.60/0.77  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.60/0.77  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.60/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.77  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.60/0.77  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.60/0.77  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.60/0.77  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.60/0.77  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.60/0.77  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.60/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.77  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.60/0.77  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.60/0.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.60/0.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.60/0.77  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.60/0.77  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.60/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.60/0.77  thf(t35_tex_2, conjecture,
% 0.60/0.77    (![A:$i]:
% 0.60/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.77       ( ![B:$i]:
% 0.60/0.77         ( ( ( v1_xboole_0 @ B ) & 
% 0.60/0.77             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.60/0.77           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.60/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.77    (~( ![A:$i]:
% 0.60/0.77        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.60/0.77            ( l1_pre_topc @ A ) ) =>
% 0.60/0.77          ( ![B:$i]:
% 0.60/0.77            ( ( ( v1_xboole_0 @ B ) & 
% 0.60/0.77                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.60/0.77              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.60/0.77    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 0.60/0.77  thf('0', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf('1', plain, ((v1_xboole_0 @ sk_B)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf(l13_xboole_0, axiom,
% 0.60/0.77    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.60/0.77  thf('2', plain,
% 0.60/0.77      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.60/0.77      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.60/0.77  thf('3', plain, (((sk_B) = (k1_xboole_0))),
% 0.60/0.77      inference('sup-', [status(thm)], ['1', '2'])).
% 0.60/0.77  thf('4', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.60/0.77      inference('demod', [status(thm)], ['0', '3'])).
% 0.60/0.77  thf('5', plain,
% 0.60/0.77      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.60/0.77      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.60/0.77  thf(t4_subset_1, axiom,
% 0.60/0.77    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.60/0.77  thf('6', plain,
% 0.60/0.77      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 0.60/0.77      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.60/0.77  thf(d5_tex_2, axiom,
% 0.60/0.77    (![A:$i]:
% 0.60/0.77     ( ( l1_pre_topc @ A ) =>
% 0.60/0.77       ( ![B:$i]:
% 0.60/0.77         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.77           ( ( v2_tex_2 @ B @ A ) <=>
% 0.60/0.77             ( ![C:$i]:
% 0.60/0.77               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.77                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.60/0.77                      ( ![D:$i]:
% 0.60/0.77                        ( ( m1_subset_1 @
% 0.60/0.77                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.77                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.60/0.77                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.60/0.77                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.60/0.77  thf('7', plain,
% 0.60/0.77      (![X20 : $i, X21 : $i]:
% 0.60/0.77         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.60/0.77          | (r1_tarski @ (sk_C @ X20 @ X21) @ X20)
% 0.60/0.77          | (v2_tex_2 @ X20 @ X21)
% 0.60/0.77          | ~ (l1_pre_topc @ X21))),
% 0.60/0.77      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.60/0.77  thf('8', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         (~ (l1_pre_topc @ X0)
% 0.60/0.77          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.60/0.77          | (r1_tarski @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.60/0.77      inference('sup-', [status(thm)], ['6', '7'])).
% 0.60/0.77  thf(t12_xboole_1, axiom,
% 0.60/0.77    (![A:$i,B:$i]:
% 0.60/0.77     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.60/0.77  thf('9', plain,
% 0.60/0.77      (![X1 : $i, X2 : $i]:
% 0.60/0.77         (((k2_xboole_0 @ X2 @ X1) = (X1)) | ~ (r1_tarski @ X2 @ X1))),
% 0.60/0.77      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.60/0.77  thf('10', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.60/0.77          | ~ (l1_pre_topc @ X0)
% 0.60/0.77          | ((k2_xboole_0 @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.60/0.77              = (k1_xboole_0)))),
% 0.60/0.77      inference('sup-', [status(thm)], ['8', '9'])).
% 0.60/0.77  thf(t1_boole, axiom,
% 0.60/0.77    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.60/0.77  thf('11', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.60/0.77      inference('cnf', [status(esa)], [t1_boole])).
% 0.60/0.77  thf('12', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.60/0.77          | ~ (l1_pre_topc @ X0)
% 0.60/0.77          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.60/0.77      inference('demod', [status(thm)], ['10', '11'])).
% 0.60/0.77  thf('13', plain,
% 0.60/0.77      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.60/0.77      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.60/0.77  thf('14', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.60/0.77      inference('demod', [status(thm)], ['0', '3'])).
% 0.60/0.77  thf('15', plain,
% 0.60/0.77      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.60/0.77      inference('sup-', [status(thm)], ['13', '14'])).
% 0.60/0.77  thf('16', plain,
% 0.60/0.77      ((((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))
% 0.60/0.77        | ~ (l1_pre_topc @ sk_A)
% 0.60/0.77        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.60/0.77      inference('sup-', [status(thm)], ['12', '15'])).
% 0.60/0.77  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf('18', plain, ((v1_xboole_0 @ sk_B)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf('19', plain, (((sk_B) = (k1_xboole_0))),
% 0.60/0.77      inference('sup-', [status(thm)], ['1', '2'])).
% 0.60/0.77  thf('20', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.60/0.77      inference('demod', [status(thm)], ['18', '19'])).
% 0.60/0.77  thf('21', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.60/0.77      inference('demod', [status(thm)], ['16', '17', '20'])).
% 0.60/0.77  thf('22', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         (((sk_C @ X0 @ sk_A) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.60/0.77      inference('sup+', [status(thm)], ['5', '21'])).
% 0.60/0.77  thf(fc10_tops_1, axiom,
% 0.60/0.77    (![A:$i]:
% 0.60/0.77     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.60/0.77       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.60/0.77  thf('23', plain,
% 0.60/0.77      (![X19 : $i]:
% 0.60/0.77         ((v3_pre_topc @ (k2_struct_0 @ X19) @ X19)
% 0.60/0.77          | ~ (l1_pre_topc @ X19)
% 0.60/0.77          | ~ (v2_pre_topc @ X19))),
% 0.60/0.77      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.60/0.77  thf(d3_struct_0, axiom,
% 0.60/0.77    (![A:$i]:
% 0.60/0.77     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.60/0.77  thf('24', plain,
% 0.60/0.77      (![X17 : $i]:
% 0.60/0.77         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.60/0.77      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.60/0.77  thf(dt_k2_subset_1, axiom,
% 0.60/0.77    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.60/0.77  thf('25', plain,
% 0.60/0.77      (![X9 : $i]: (m1_subset_1 @ (k2_subset_1 @ X9) @ (k1_zfmisc_1 @ X9))),
% 0.60/0.77      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.60/0.77  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.60/0.77  thf('26', plain, (![X8 : $i]: ((k2_subset_1 @ X8) = (X8))),
% 0.60/0.77      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.60/0.77  thf('27', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 0.60/0.77      inference('demod', [status(thm)], ['25', '26'])).
% 0.60/0.77  thf('28', plain,
% 0.60/0.77      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 0.60/0.77      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.60/0.77  thf('29', plain,
% 0.60/0.77      (![X20 : $i, X21 : $i, X23 : $i]:
% 0.60/0.77         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.60/0.77          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.60/0.77          | ~ (v3_pre_topc @ X23 @ X21)
% 0.60/0.77          | ((k9_subset_1 @ (u1_struct_0 @ X21) @ X20 @ X23)
% 0.60/0.77              != (sk_C @ X20 @ X21))
% 0.60/0.77          | (v2_tex_2 @ X20 @ X21)
% 0.60/0.77          | ~ (l1_pre_topc @ X21))),
% 0.60/0.77      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.60/0.77  thf('30', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         (~ (l1_pre_topc @ X0)
% 0.60/0.77          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.60/0.77          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 0.60/0.77              != (sk_C @ k1_xboole_0 @ X0))
% 0.60/0.77          | ~ (v3_pre_topc @ X1 @ X0)
% 0.60/0.77          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.60/0.77      inference('sup-', [status(thm)], ['28', '29'])).
% 0.60/0.77  thf('31', plain,
% 0.60/0.77      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 0.60/0.77      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.60/0.77  thf(commutativity_k9_subset_1, axiom,
% 0.60/0.77    (![A:$i,B:$i,C:$i]:
% 0.60/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.60/0.77       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.60/0.77  thf('32', plain,
% 0.60/0.77      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.60/0.77         (((k9_subset_1 @ X5 @ X7 @ X6) = (k9_subset_1 @ X5 @ X6 @ X7))
% 0.60/0.77          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.60/0.77      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.60/0.77  thf('33', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.60/0.77           = (k9_subset_1 @ X0 @ k1_xboole_0 @ X1))),
% 0.60/0.77      inference('sup-', [status(thm)], ['31', '32'])).
% 0.60/0.77  thf('34', plain,
% 0.60/0.77      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 0.60/0.77      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.60/0.77  thf(redefinition_k9_subset_1, axiom,
% 0.60/0.77    (![A:$i,B:$i,C:$i]:
% 0.60/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.60/0.77       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.60/0.77  thf('35', plain,
% 0.60/0.77      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.60/0.77         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 0.60/0.77          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.60/0.77      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.60/0.77  thf('36', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.60/0.77           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 0.60/0.77      inference('sup-', [status(thm)], ['34', '35'])).
% 0.60/0.77  thf(t2_boole, axiom,
% 0.60/0.77    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.60/0.77  thf('37', plain,
% 0.60/0.77      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.60/0.77      inference('cnf', [status(esa)], [t2_boole])).
% 0.60/0.77  thf('38', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.60/0.77      inference('demod', [status(thm)], ['36', '37'])).
% 0.60/0.77  thf('39', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         ((k1_xboole_0) = (k9_subset_1 @ X0 @ k1_xboole_0 @ X1))),
% 0.60/0.77      inference('demod', [status(thm)], ['33', '38'])).
% 0.60/0.77  thf('40', plain,
% 0.60/0.77      (![X0 : $i, X1 : $i]:
% 0.60/0.77         (~ (l1_pre_topc @ X0)
% 0.60/0.77          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.60/0.77          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.60/0.77          | ~ (v3_pre_topc @ X1 @ X0)
% 0.60/0.77          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.60/0.77      inference('demod', [status(thm)], ['30', '39'])).
% 0.60/0.77  thf('41', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         (~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.60/0.77          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.60/0.77          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.60/0.77          | ~ (l1_pre_topc @ X0))),
% 0.60/0.77      inference('sup-', [status(thm)], ['27', '40'])).
% 0.60/0.77  thf('42', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 0.60/0.77          | ~ (l1_struct_0 @ X0)
% 0.60/0.77          | ~ (l1_pre_topc @ X0)
% 0.60/0.77          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.60/0.77          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0)))),
% 0.60/0.77      inference('sup-', [status(thm)], ['24', '41'])).
% 0.60/0.77  thf('43', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         (~ (v2_pre_topc @ X0)
% 0.60/0.77          | ~ (l1_pre_topc @ X0)
% 0.60/0.77          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.60/0.77          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.60/0.77          | ~ (l1_pre_topc @ X0)
% 0.60/0.77          | ~ (l1_struct_0 @ X0))),
% 0.60/0.77      inference('sup-', [status(thm)], ['23', '42'])).
% 0.60/0.77  thf('44', plain,
% 0.60/0.77      (![X0 : $i]:
% 0.60/0.77         (~ (l1_struct_0 @ X0)
% 0.60/0.77          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.60/0.77          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.60/0.77          | ~ (l1_pre_topc @ X0)
% 0.60/0.77          | ~ (v2_pre_topc @ X0))),
% 0.60/0.77      inference('simplify', [status(thm)], ['43'])).
% 0.60/0.77  thf('45', plain,
% 0.60/0.77      ((((k1_xboole_0) != (k1_xboole_0))
% 0.60/0.77        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.60/0.77        | ~ (v2_pre_topc @ sk_A)
% 0.60/0.77        | ~ (l1_pre_topc @ sk_A)
% 0.60/0.77        | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 0.60/0.77        | ~ (l1_struct_0 @ sk_A))),
% 0.60/0.77      inference('sup-', [status(thm)], ['22', '44'])).
% 0.60/0.77  thf('46', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.60/0.77      inference('demod', [status(thm)], ['18', '19'])).
% 0.60/0.77  thf('47', plain, ((v2_pre_topc @ sk_A)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.77  thf(dt_l1_pre_topc, axiom,
% 0.60/0.77    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.60/0.77  thf('50', plain,
% 0.60/0.77      (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.60/0.77      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.60/0.77  thf('51', plain, ((l1_struct_0 @ sk_A)),
% 0.60/0.77      inference('sup-', [status(thm)], ['49', '50'])).
% 0.60/0.77  thf('52', plain,
% 0.60/0.77      ((((k1_xboole_0) != (k1_xboole_0)) | (v2_tex_2 @ k1_xboole_0 @ sk_A))),
% 0.60/0.77      inference('demod', [status(thm)], ['45', '46', '47', '48', '51'])).
% 0.60/0.77  thf('53', plain, ((v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.60/0.77      inference('simplify', [status(thm)], ['52'])).
% 0.60/0.77  thf('54', plain, ($false), inference('demod', [status(thm)], ['4', '53'])).
% 0.60/0.77  
% 0.60/0.77  % SZS output end Refutation
% 0.60/0.77  
% 0.60/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
