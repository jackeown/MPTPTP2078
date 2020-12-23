%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QIuHLcr62H

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:38 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 130 expanded)
%              Number of leaves         :   28 (  52 expanded)
%              Depth                    :   13
%              Number of atoms          :  519 ( 994 expanded)
%              Number of equality atoms :   31 (  44 expanded)
%              Maximal formula depth    :   19 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

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

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X15 @ X14 ) @ X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k1_tops_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('10',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_xboole_0 @ X2 @ X1 )
        = X1 )
      | ~ ( r1_tarski @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_xboole_0 @ ( k1_tops_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('15',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X12 @ X13 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k1_tops_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_pre_topc @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','19'])).

thf('21',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('24',plain,(
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

thf('25',plain,(
    ! [X16: $i,X17: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v3_pre_topc @ X19 @ X17 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X17 ) @ X16 @ X19 )
       != ( sk_C @ X16 @ X17 ) )
      | ( v2_tex_2 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ X1 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ k1_xboole_0 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k9_subset_1 @ X7 @ X5 @ X6 )
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('31',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['27','32'])).

thf('34',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0
     != ( sk_C @ k1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','33'])).

thf('35',plain,(
    v1_xboole_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('37',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('40',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( r1_tarski @ ( sk_C @ X16 @ X17 ) @ X16 )
      | ( v2_tex_2 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_xboole_0 @ X2 @ X1 )
        = X1 )
      | ~ ( r1_tarski @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_xboole_0 @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('47',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( sk_C @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['35','36'])).

thf('52',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','37','38','52'])).

thf('54',plain,(
    v2_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['4','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QIuHLcr62H
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:15:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.21/0.34  % Python version: Python 3.6.8
% 0.21/0.34  % Running in FO mode
% 0.54/0.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.54/0.71  % Solved by: fo/fo7.sh
% 0.54/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.71  % done 382 iterations in 0.266s
% 0.54/0.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.54/0.71  % SZS output start Refutation
% 0.54/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.71  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.54/0.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.54/0.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.54/0.71  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.54/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.71  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.54/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.71  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.54/0.71  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.54/0.71  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.54/0.71  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.54/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.71  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.54/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.54/0.71  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.54/0.71  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.54/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.71  thf(t35_tex_2, conjecture,
% 0.54/0.71    (![A:$i]:
% 0.54/0.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.54/0.71       ( ![B:$i]:
% 0.54/0.71         ( ( ( v1_xboole_0 @ B ) & 
% 0.54/0.71             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.54/0.71           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.54/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.71    (~( ![A:$i]:
% 0.54/0.71        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.54/0.71            ( l1_pre_topc @ A ) ) =>
% 0.54/0.71          ( ![B:$i]:
% 0.54/0.71            ( ( ( v1_xboole_0 @ B ) & 
% 0.54/0.71                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.54/0.71              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.54/0.71    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 0.54/0.71  thf('0', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf('1', plain, ((v1_xboole_0 @ sk_B)),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf(l13_xboole_0, axiom,
% 0.54/0.71    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.54/0.71  thf('2', plain,
% 0.54/0.71      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.54/0.71      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.54/0.71  thf('3', plain, (((sk_B) = (k1_xboole_0))),
% 0.54/0.71      inference('sup-', [status(thm)], ['1', '2'])).
% 0.54/0.71  thf('4', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.54/0.71      inference('demod', [status(thm)], ['0', '3'])).
% 0.54/0.71  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf('6', plain,
% 0.54/0.71      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.54/0.71      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.54/0.71  thf(t4_subset_1, axiom,
% 0.54/0.71    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.54/0.71  thf('7', plain,
% 0.54/0.71      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.54/0.71      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.54/0.71  thf(t44_tops_1, axiom,
% 0.54/0.71    (![A:$i]:
% 0.54/0.71     ( ( l1_pre_topc @ A ) =>
% 0.54/0.71       ( ![B:$i]:
% 0.54/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.71           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.54/0.71  thf('8', plain,
% 0.54/0.71      (![X14 : $i, X15 : $i]:
% 0.54/0.71         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.54/0.71          | (r1_tarski @ (k1_tops_1 @ X15 @ X14) @ X14)
% 0.54/0.71          | ~ (l1_pre_topc @ X15))),
% 0.54/0.71      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.54/0.71  thf('9', plain,
% 0.54/0.71      (![X0 : $i]:
% 0.54/0.71         (~ (l1_pre_topc @ X0)
% 0.54/0.71          | (r1_tarski @ (k1_tops_1 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.54/0.71      inference('sup-', [status(thm)], ['7', '8'])).
% 0.54/0.71  thf(t12_xboole_1, axiom,
% 0.54/0.71    (![A:$i,B:$i]:
% 0.54/0.71     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.54/0.71  thf('10', plain,
% 0.54/0.71      (![X1 : $i, X2 : $i]:
% 0.54/0.71         (((k2_xboole_0 @ X2 @ X1) = (X1)) | ~ (r1_tarski @ X2 @ X1))),
% 0.54/0.71      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.54/0.71  thf('11', plain,
% 0.54/0.71      (![X0 : $i]:
% 0.54/0.71         (~ (l1_pre_topc @ X0)
% 0.54/0.71          | ((k2_xboole_0 @ (k1_tops_1 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.54/0.71              = (k1_xboole_0)))),
% 0.54/0.71      inference('sup-', [status(thm)], ['9', '10'])).
% 0.54/0.71  thf(t1_boole, axiom,
% 0.54/0.71    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.54/0.71  thf('12', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.54/0.71      inference('cnf', [status(esa)], [t1_boole])).
% 0.54/0.71  thf('13', plain,
% 0.54/0.71      (![X0 : $i]:
% 0.54/0.71         (~ (l1_pre_topc @ X0)
% 0.54/0.71          | ((k1_tops_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.54/0.71      inference('demod', [status(thm)], ['11', '12'])).
% 0.54/0.71  thf('14', plain,
% 0.54/0.71      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.54/0.71      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.54/0.71  thf(fc9_tops_1, axiom,
% 0.54/0.71    (![A:$i,B:$i]:
% 0.54/0.71     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.54/0.71         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.54/0.71       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.54/0.71  thf('15', plain,
% 0.54/0.71      (![X12 : $i, X13 : $i]:
% 0.54/0.71         (~ (l1_pre_topc @ X12)
% 0.54/0.71          | ~ (v2_pre_topc @ X12)
% 0.54/0.71          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.54/0.71          | (v3_pre_topc @ (k1_tops_1 @ X12 @ X13) @ X12))),
% 0.54/0.71      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.54/0.71  thf('16', plain,
% 0.54/0.71      (![X0 : $i]:
% 0.54/0.71         ((v3_pre_topc @ (k1_tops_1 @ X0 @ k1_xboole_0) @ X0)
% 0.54/0.71          | ~ (v2_pre_topc @ X0)
% 0.54/0.71          | ~ (l1_pre_topc @ X0))),
% 0.54/0.71      inference('sup-', [status(thm)], ['14', '15'])).
% 0.54/0.71  thf('17', plain,
% 0.54/0.71      (![X0 : $i]:
% 0.54/0.71         ((v3_pre_topc @ k1_xboole_0 @ X0)
% 0.54/0.71          | ~ (l1_pre_topc @ X0)
% 0.54/0.71          | ~ (l1_pre_topc @ X0)
% 0.54/0.71          | ~ (v2_pre_topc @ X0))),
% 0.54/0.71      inference('sup+', [status(thm)], ['13', '16'])).
% 0.54/0.71  thf('18', plain,
% 0.54/0.71      (![X0 : $i]:
% 0.54/0.71         (~ (v2_pre_topc @ X0)
% 0.54/0.71          | ~ (l1_pre_topc @ X0)
% 0.54/0.71          | (v3_pre_topc @ k1_xboole_0 @ X0))),
% 0.54/0.71      inference('simplify', [status(thm)], ['17'])).
% 0.54/0.71  thf('19', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((v3_pre_topc @ X0 @ X1)
% 0.54/0.71          | ~ (v1_xboole_0 @ X0)
% 0.54/0.71          | ~ (l1_pre_topc @ X1)
% 0.54/0.71          | ~ (v2_pre_topc @ X1))),
% 0.54/0.71      inference('sup+', [status(thm)], ['6', '18'])).
% 0.54/0.71  thf('20', plain,
% 0.54/0.71      (![X0 : $i]:
% 0.54/0.71         (~ (v2_pre_topc @ sk_A)
% 0.54/0.71          | ~ (v1_xboole_0 @ X0)
% 0.54/0.71          | (v3_pre_topc @ X0 @ sk_A))),
% 0.54/0.71      inference('sup-', [status(thm)], ['5', '19'])).
% 0.54/0.71  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf('22', plain,
% 0.54/0.71      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v3_pre_topc @ X0 @ sk_A))),
% 0.54/0.71      inference('demod', [status(thm)], ['20', '21'])).
% 0.54/0.71  thf('23', plain,
% 0.54/0.71      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.54/0.71      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.54/0.71  thf('24', plain,
% 0.54/0.71      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.54/0.71      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.54/0.71  thf(d5_tex_2, axiom,
% 0.54/0.71    (![A:$i]:
% 0.54/0.71     ( ( l1_pre_topc @ A ) =>
% 0.54/0.71       ( ![B:$i]:
% 0.54/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.71           ( ( v2_tex_2 @ B @ A ) <=>
% 0.54/0.71             ( ![C:$i]:
% 0.54/0.71               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.71                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.54/0.71                      ( ![D:$i]:
% 0.54/0.71                        ( ( m1_subset_1 @
% 0.54/0.71                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.71                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.54/0.71                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.54/0.71                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.54/0.71  thf('25', plain,
% 0.54/0.71      (![X16 : $i, X17 : $i, X19 : $i]:
% 0.54/0.71         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.54/0.71          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.54/0.71          | ~ (v3_pre_topc @ X19 @ X17)
% 0.54/0.71          | ((k9_subset_1 @ (u1_struct_0 @ X17) @ X16 @ X19)
% 0.54/0.71              != (sk_C @ X16 @ X17))
% 0.54/0.71          | (v2_tex_2 @ X16 @ X17)
% 0.54/0.71          | ~ (l1_pre_topc @ X17))),
% 0.54/0.71      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.54/0.71  thf('26', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         (~ (l1_pre_topc @ X0)
% 0.54/0.71          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.54/0.71          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 0.54/0.71              != (sk_C @ k1_xboole_0 @ X0))
% 0.54/0.71          | ~ (v3_pre_topc @ X1 @ X0)
% 0.54/0.71          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.54/0.71      inference('sup-', [status(thm)], ['24', '25'])).
% 0.54/0.71  thf('27', plain,
% 0.54/0.71      (![X0 : $i]:
% 0.54/0.71         (~ (v3_pre_topc @ k1_xboole_0 @ X0)
% 0.54/0.71          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ k1_xboole_0)
% 0.54/0.71              != (sk_C @ k1_xboole_0 @ X0))
% 0.54/0.71          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.54/0.71          | ~ (l1_pre_topc @ X0))),
% 0.54/0.71      inference('sup-', [status(thm)], ['23', '26'])).
% 0.54/0.71  thf('28', plain,
% 0.54/0.71      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.54/0.71      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.54/0.71  thf(redefinition_k9_subset_1, axiom,
% 0.54/0.71    (![A:$i,B:$i,C:$i]:
% 0.54/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.54/0.71       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.54/0.71  thf('29', plain,
% 0.54/0.71      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.54/0.71         (((k9_subset_1 @ X7 @ X5 @ X6) = (k3_xboole_0 @ X5 @ X6))
% 0.54/0.71          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.54/0.71      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.54/0.71  thf('30', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.54/0.71           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 0.54/0.71      inference('sup-', [status(thm)], ['28', '29'])).
% 0.54/0.71  thf(t2_boole, axiom,
% 0.54/0.71    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.54/0.71  thf('31', plain,
% 0.54/0.71      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.71      inference('cnf', [status(esa)], [t2_boole])).
% 0.54/0.71  thf('32', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.71      inference('demod', [status(thm)], ['30', '31'])).
% 0.54/0.71  thf('33', plain,
% 0.54/0.71      (![X0 : $i]:
% 0.54/0.71         (~ (v3_pre_topc @ k1_xboole_0 @ X0)
% 0.54/0.71          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.54/0.71          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.54/0.71          | ~ (l1_pre_topc @ X0))),
% 0.54/0.71      inference('demod', [status(thm)], ['27', '32'])).
% 0.54/0.71  thf('34', plain,
% 0.54/0.71      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.54/0.71        | ~ (l1_pre_topc @ sk_A)
% 0.54/0.71        | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 0.54/0.71        | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ sk_A)))),
% 0.54/0.71      inference('sup-', [status(thm)], ['22', '33'])).
% 0.54/0.71  thf('35', plain, ((v1_xboole_0 @ sk_B)),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf('36', plain, (((sk_B) = (k1_xboole_0))),
% 0.54/0.71      inference('sup-', [status(thm)], ['1', '2'])).
% 0.54/0.71  thf('37', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.54/0.71      inference('demod', [status(thm)], ['35', '36'])).
% 0.54/0.71  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf('39', plain,
% 0.54/0.71      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.54/0.71      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.54/0.71  thf('40', plain,
% 0.54/0.71      (![X16 : $i, X17 : $i]:
% 0.54/0.71         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.54/0.71          | (r1_tarski @ (sk_C @ X16 @ X17) @ X16)
% 0.54/0.71          | (v2_tex_2 @ X16 @ X17)
% 0.54/0.71          | ~ (l1_pre_topc @ X17))),
% 0.54/0.71      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.54/0.71  thf('41', plain,
% 0.54/0.71      (![X0 : $i]:
% 0.54/0.71         (~ (l1_pre_topc @ X0)
% 0.54/0.71          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.54/0.71          | (r1_tarski @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.54/0.71      inference('sup-', [status(thm)], ['39', '40'])).
% 0.54/0.71  thf('42', plain,
% 0.54/0.71      (![X1 : $i, X2 : $i]:
% 0.54/0.71         (((k2_xboole_0 @ X2 @ X1) = (X1)) | ~ (r1_tarski @ X2 @ X1))),
% 0.54/0.71      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.54/0.71  thf('43', plain,
% 0.54/0.71      (![X0 : $i]:
% 0.54/0.71         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.54/0.71          | ~ (l1_pre_topc @ X0)
% 0.54/0.71          | ((k2_xboole_0 @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.54/0.71              = (k1_xboole_0)))),
% 0.54/0.71      inference('sup-', [status(thm)], ['41', '42'])).
% 0.54/0.71  thf('44', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.54/0.71      inference('cnf', [status(esa)], [t1_boole])).
% 0.54/0.71  thf('45', plain,
% 0.54/0.71      (![X0 : $i]:
% 0.54/0.71         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.54/0.71          | ~ (l1_pre_topc @ X0)
% 0.54/0.71          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.54/0.71      inference('demod', [status(thm)], ['43', '44'])).
% 0.54/0.71  thf('46', plain,
% 0.54/0.71      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.54/0.71      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.54/0.71  thf('47', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.54/0.71      inference('demod', [status(thm)], ['0', '3'])).
% 0.54/0.71  thf('48', plain,
% 0.54/0.71      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.54/0.71      inference('sup-', [status(thm)], ['46', '47'])).
% 0.54/0.71  thf('49', plain,
% 0.54/0.72      ((((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))
% 0.54/0.72        | ~ (l1_pre_topc @ sk_A)
% 0.54/0.72        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.54/0.72      inference('sup-', [status(thm)], ['45', '48'])).
% 0.54/0.72  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf('51', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.54/0.72      inference('demod', [status(thm)], ['35', '36'])).
% 0.54/0.72  thf('52', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.54/0.72      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.54/0.72  thf('53', plain,
% 0.54/0.72      (((v2_tex_2 @ k1_xboole_0 @ sk_A) | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.54/0.72      inference('demod', [status(thm)], ['34', '37', '38', '52'])).
% 0.54/0.72  thf('54', plain, ((v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.54/0.72      inference('simplify', [status(thm)], ['53'])).
% 0.54/0.72  thf('55', plain, ($false), inference('demod', [status(thm)], ['4', '54'])).
% 0.54/0.72  
% 0.54/0.72  % SZS output end Refutation
% 0.54/0.72  
% 0.54/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
