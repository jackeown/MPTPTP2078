%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8C1wq2IHH7

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:38 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 134 expanded)
%              Number of leaves         :   26 (  52 expanded)
%              Depth                    :   15
%              Number of atoms          :  537 (1029 expanded)
%              Number of equality atoms :   30 (  46 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf('7',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('8',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X15 @ X14 ) @ X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k1_tops_1 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('13',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_tops_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tops_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('18',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X12 @ X13 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v3_pre_topc @ ( k1_tops_1 @ X0 @ X1 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v3_pre_topc @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v3_pre_topc @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','22'])).

thf('24',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v3_pre_topc @ X1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['25'])).

thf('27',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('28',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
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

thf('29',plain,(
    ! [X16: $i,X17: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v3_pre_topc @ X19 @ X17 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X17 ) @ X16 @ X19 )
       != ( sk_C @ X16 @ X17 ) )
      | ( v2_tex_2 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
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
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ k1_xboole_0 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('33',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( ( k9_subset_1 @ X5 @ X3 @ X4 )
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('35',plain,(
    ! [X1: $i] :
      ( ( k3_xboole_0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['31','36'])).

thf('38',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0
     != ( sk_C @ k1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','37'])).

thf('39',plain,(
    v1_xboole_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('41',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('44',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( r1_tarski @ ( sk_C @ X16 @ X17 ) @ X16 )
      | ( v2_tex_2 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('49',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( sk_C @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['39','40'])).

thf('54',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,
    ( ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','41','42','54'])).

thf('56',plain,(
    v2_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['4','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8C1wq2IHH7
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:26:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.34/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.34/0.60  % Solved by: fo/fo7.sh
% 0.34/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.60  % done 228 iterations in 0.134s
% 0.34/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.34/0.60  % SZS output start Refutation
% 0.34/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.34/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.34/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.34/0.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.34/0.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.34/0.60  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.34/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.34/0.60  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.34/0.60  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.34/0.60  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.34/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.34/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.34/0.60  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.34/0.60  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.34/0.60  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.34/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.34/0.60  thf(t35_tex_2, conjecture,
% 0.34/0.60    (![A:$i]:
% 0.34/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.34/0.60       ( ![B:$i]:
% 0.34/0.60         ( ( ( v1_xboole_0 @ B ) & 
% 0.34/0.60             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.34/0.60           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.34/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.60    (~( ![A:$i]:
% 0.34/0.60        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.34/0.60            ( l1_pre_topc @ A ) ) =>
% 0.34/0.60          ( ![B:$i]:
% 0.34/0.60            ( ( ( v1_xboole_0 @ B ) & 
% 0.34/0.60                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.34/0.60              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.34/0.60    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 0.34/0.60  thf('0', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.34/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.60  thf('1', plain, ((v1_xboole_0 @ sk_B)),
% 0.34/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.60  thf(l13_xboole_0, axiom,
% 0.34/0.60    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.34/0.60  thf('2', plain,
% 0.34/0.60      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.34/0.60      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.34/0.60  thf('3', plain, (((sk_B) = (k1_xboole_0))),
% 0.34/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.34/0.60  thf('4', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.34/0.60      inference('demod', [status(thm)], ['0', '3'])).
% 0.34/0.60  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.60  thf('6', plain,
% 0.34/0.60      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.34/0.60      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.34/0.60  thf('7', plain,
% 0.34/0.60      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.34/0.60      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.34/0.60  thf(t4_subset_1, axiom,
% 0.34/0.60    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.34/0.60  thf('8', plain,
% 0.34/0.60      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.34/0.60      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.34/0.60  thf('9', plain,
% 0.34/0.60      (![X0 : $i, X1 : $i]:
% 0.34/0.60         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.34/0.60      inference('sup+', [status(thm)], ['7', '8'])).
% 0.34/0.60  thf(t44_tops_1, axiom,
% 0.34/0.60    (![A:$i]:
% 0.34/0.60     ( ( l1_pre_topc @ A ) =>
% 0.34/0.60       ( ![B:$i]:
% 0.34/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.60           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.34/0.60  thf('10', plain,
% 0.34/0.60      (![X14 : $i, X15 : $i]:
% 0.34/0.60         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.34/0.60          | (r1_tarski @ (k1_tops_1 @ X15 @ X14) @ X14)
% 0.34/0.60          | ~ (l1_pre_topc @ X15))),
% 0.34/0.60      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.34/0.60  thf('11', plain,
% 0.34/0.60      (![X0 : $i, X1 : $i]:
% 0.34/0.60         (~ (v1_xboole_0 @ X1)
% 0.34/0.60          | ~ (l1_pre_topc @ X0)
% 0.34/0.60          | (r1_tarski @ (k1_tops_1 @ X0 @ X1) @ X1))),
% 0.34/0.60      inference('sup-', [status(thm)], ['9', '10'])).
% 0.34/0.60  thf('12', plain,
% 0.34/0.60      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.34/0.60      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.34/0.60  thf(t3_xboole_1, axiom,
% 0.34/0.60    (![A:$i]:
% 0.34/0.60     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.34/0.60  thf('13', plain,
% 0.34/0.60      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ k1_xboole_0))),
% 0.34/0.60      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.34/0.60  thf('14', plain,
% 0.34/0.60      (![X0 : $i, X1 : $i]:
% 0.34/0.60         (~ (r1_tarski @ X1 @ X0)
% 0.34/0.60          | ~ (v1_xboole_0 @ X0)
% 0.34/0.60          | ((X1) = (k1_xboole_0)))),
% 0.34/0.60      inference('sup-', [status(thm)], ['12', '13'])).
% 0.34/0.60  thf('15', plain,
% 0.34/0.60      (![X0 : $i, X1 : $i]:
% 0.34/0.60         (~ (l1_pre_topc @ X1)
% 0.34/0.60          | ~ (v1_xboole_0 @ X0)
% 0.34/0.60          | ((k1_tops_1 @ X1 @ X0) = (k1_xboole_0))
% 0.34/0.60          | ~ (v1_xboole_0 @ X0))),
% 0.34/0.60      inference('sup-', [status(thm)], ['11', '14'])).
% 0.34/0.60  thf('16', plain,
% 0.34/0.60      (![X0 : $i, X1 : $i]:
% 0.34/0.60         (((k1_tops_1 @ X1 @ X0) = (k1_xboole_0))
% 0.34/0.60          | ~ (v1_xboole_0 @ X0)
% 0.34/0.60          | ~ (l1_pre_topc @ X1))),
% 0.34/0.60      inference('simplify', [status(thm)], ['15'])).
% 0.34/0.60  thf('17', plain,
% 0.34/0.60      (![X0 : $i, X1 : $i]:
% 0.34/0.60         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.34/0.60      inference('sup+', [status(thm)], ['7', '8'])).
% 0.34/0.60  thf(fc9_tops_1, axiom,
% 0.34/0.60    (![A:$i,B:$i]:
% 0.34/0.60     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.34/0.60         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.34/0.60       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.34/0.60  thf('18', plain,
% 0.34/0.60      (![X12 : $i, X13 : $i]:
% 0.34/0.60         (~ (l1_pre_topc @ X12)
% 0.34/0.60          | ~ (v2_pre_topc @ X12)
% 0.34/0.60          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.34/0.60          | (v3_pre_topc @ (k1_tops_1 @ X12 @ X13) @ X12))),
% 0.34/0.60      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.34/0.60  thf('19', plain,
% 0.34/0.60      (![X0 : $i, X1 : $i]:
% 0.34/0.60         (~ (v1_xboole_0 @ X1)
% 0.34/0.60          | (v3_pre_topc @ (k1_tops_1 @ X0 @ X1) @ X0)
% 0.34/0.60          | ~ (v2_pre_topc @ X0)
% 0.34/0.60          | ~ (l1_pre_topc @ X0))),
% 0.34/0.60      inference('sup-', [status(thm)], ['17', '18'])).
% 0.34/0.60  thf('20', plain,
% 0.34/0.60      (![X0 : $i, X1 : $i]:
% 0.34/0.60         ((v3_pre_topc @ k1_xboole_0 @ X0)
% 0.34/0.60          | ~ (l1_pre_topc @ X0)
% 0.34/0.60          | ~ (v1_xboole_0 @ X1)
% 0.34/0.60          | ~ (l1_pre_topc @ X0)
% 0.34/0.60          | ~ (v2_pre_topc @ X0)
% 0.34/0.60          | ~ (v1_xboole_0 @ X1))),
% 0.34/0.60      inference('sup+', [status(thm)], ['16', '19'])).
% 0.34/0.60  thf('21', plain,
% 0.34/0.60      (![X0 : $i, X1 : $i]:
% 0.34/0.60         (~ (v2_pre_topc @ X0)
% 0.34/0.60          | ~ (v1_xboole_0 @ X1)
% 0.34/0.60          | ~ (l1_pre_topc @ X0)
% 0.34/0.60          | (v3_pre_topc @ k1_xboole_0 @ X0))),
% 0.34/0.60      inference('simplify', [status(thm)], ['20'])).
% 0.34/0.60  thf('22', plain,
% 0.34/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.60         ((v3_pre_topc @ X0 @ X1)
% 0.34/0.60          | ~ (v1_xboole_0 @ X0)
% 0.34/0.60          | ~ (l1_pre_topc @ X1)
% 0.34/0.60          | ~ (v1_xboole_0 @ X2)
% 0.34/0.60          | ~ (v2_pre_topc @ X1))),
% 0.34/0.60      inference('sup+', [status(thm)], ['6', '21'])).
% 0.34/0.60  thf('23', plain,
% 0.34/0.60      (![X0 : $i, X1 : $i]:
% 0.34/0.60         (~ (v2_pre_topc @ sk_A)
% 0.34/0.60          | ~ (v1_xboole_0 @ X0)
% 0.34/0.60          | ~ (v1_xboole_0 @ X1)
% 0.34/0.60          | (v3_pre_topc @ X1 @ sk_A))),
% 0.34/0.60      inference('sup-', [status(thm)], ['5', '22'])).
% 0.34/0.60  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 0.34/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.60  thf('25', plain,
% 0.34/0.60      (![X0 : $i, X1 : $i]:
% 0.34/0.60         (~ (v1_xboole_0 @ X0)
% 0.34/0.60          | ~ (v1_xboole_0 @ X1)
% 0.34/0.60          | (v3_pre_topc @ X1 @ sk_A))),
% 0.34/0.60      inference('demod', [status(thm)], ['23', '24'])).
% 0.34/0.60  thf('26', plain,
% 0.34/0.60      (![X0 : $i]: ((v3_pre_topc @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.34/0.60      inference('condensation', [status(thm)], ['25'])).
% 0.34/0.60  thf('27', plain,
% 0.34/0.60      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.34/0.60      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.34/0.60  thf('28', plain,
% 0.34/0.60      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.34/0.60      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.34/0.60  thf(d5_tex_2, axiom,
% 0.34/0.60    (![A:$i]:
% 0.34/0.60     ( ( l1_pre_topc @ A ) =>
% 0.34/0.60       ( ![B:$i]:
% 0.34/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.60           ( ( v2_tex_2 @ B @ A ) <=>
% 0.34/0.60             ( ![C:$i]:
% 0.34/0.60               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.60                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.34/0.60                      ( ![D:$i]:
% 0.34/0.60                        ( ( m1_subset_1 @
% 0.34/0.60                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.60                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.34/0.60                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.34/0.60                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.34/0.60  thf('29', plain,
% 0.34/0.60      (![X16 : $i, X17 : $i, X19 : $i]:
% 0.34/0.60         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.34/0.60          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.34/0.60          | ~ (v3_pre_topc @ X19 @ X17)
% 0.34/0.60          | ((k9_subset_1 @ (u1_struct_0 @ X17) @ X16 @ X19)
% 0.34/0.60              != (sk_C @ X16 @ X17))
% 0.34/0.60          | (v2_tex_2 @ X16 @ X17)
% 0.34/0.60          | ~ (l1_pre_topc @ X17))),
% 0.34/0.60      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.34/0.60  thf('30', plain,
% 0.34/0.60      (![X0 : $i, X1 : $i]:
% 0.34/0.60         (~ (l1_pre_topc @ X0)
% 0.34/0.60          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.34/0.60          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 0.34/0.60              != (sk_C @ k1_xboole_0 @ X0))
% 0.34/0.60          | ~ (v3_pre_topc @ X1 @ X0)
% 0.34/0.60          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.34/0.60      inference('sup-', [status(thm)], ['28', '29'])).
% 0.34/0.60  thf('31', plain,
% 0.34/0.60      (![X0 : $i]:
% 0.34/0.60         (~ (v3_pre_topc @ k1_xboole_0 @ X0)
% 0.34/0.60          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ k1_xboole_0)
% 0.34/0.60              != (sk_C @ k1_xboole_0 @ X0))
% 0.34/0.60          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.34/0.60          | ~ (l1_pre_topc @ X0))),
% 0.34/0.60      inference('sup-', [status(thm)], ['27', '30'])).
% 0.34/0.60  thf('32', plain,
% 0.34/0.60      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.34/0.60      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.34/0.60  thf(redefinition_k9_subset_1, axiom,
% 0.34/0.60    (![A:$i,B:$i,C:$i]:
% 0.34/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.34/0.60       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.34/0.60  thf('33', plain,
% 0.34/0.60      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.34/0.60         (((k9_subset_1 @ X5 @ X3 @ X4) = (k3_xboole_0 @ X3 @ X4))
% 0.34/0.60          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.34/0.60      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.34/0.60  thf('34', plain,
% 0.34/0.60      (![X0 : $i, X1 : $i]:
% 0.34/0.60         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.34/0.60           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 0.34/0.60      inference('sup-', [status(thm)], ['32', '33'])).
% 0.34/0.60  thf(t2_boole, axiom,
% 0.34/0.60    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.34/0.60  thf('35', plain,
% 0.34/0.60      (![X1 : $i]: ((k3_xboole_0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.34/0.60      inference('cnf', [status(esa)], [t2_boole])).
% 0.34/0.60  thf('36', plain,
% 0.34/0.60      (![X0 : $i, X1 : $i]:
% 0.34/0.60         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.34/0.60      inference('demod', [status(thm)], ['34', '35'])).
% 0.34/0.60  thf('37', plain,
% 0.34/0.60      (![X0 : $i]:
% 0.34/0.60         (~ (v3_pre_topc @ k1_xboole_0 @ X0)
% 0.34/0.60          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.34/0.60          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.34/0.60          | ~ (l1_pre_topc @ X0))),
% 0.34/0.60      inference('demod', [status(thm)], ['31', '36'])).
% 0.34/0.60  thf('38', plain,
% 0.34/0.60      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.34/0.60        | ~ (l1_pre_topc @ sk_A)
% 0.34/0.60        | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 0.34/0.60        | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ sk_A)))),
% 0.34/0.60      inference('sup-', [status(thm)], ['26', '37'])).
% 0.34/0.60  thf('39', plain, ((v1_xboole_0 @ sk_B)),
% 0.34/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.60  thf('40', plain, (((sk_B) = (k1_xboole_0))),
% 0.34/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.34/0.60  thf('41', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.34/0.60      inference('demod', [status(thm)], ['39', '40'])).
% 0.34/0.60  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.60  thf('43', plain,
% 0.34/0.60      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.34/0.60      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.34/0.60  thf('44', plain,
% 0.34/0.60      (![X16 : $i, X17 : $i]:
% 0.34/0.60         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.34/0.60          | (r1_tarski @ (sk_C @ X16 @ X17) @ X16)
% 0.34/0.60          | (v2_tex_2 @ X16 @ X17)
% 0.34/0.60          | ~ (l1_pre_topc @ X17))),
% 0.34/0.60      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.34/0.60  thf('45', plain,
% 0.34/0.60      (![X0 : $i]:
% 0.34/0.60         (~ (l1_pre_topc @ X0)
% 0.34/0.60          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.34/0.60          | (r1_tarski @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.34/0.60      inference('sup-', [status(thm)], ['43', '44'])).
% 0.34/0.60  thf('46', plain,
% 0.34/0.60      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ k1_xboole_0))),
% 0.34/0.60      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.34/0.60  thf('47', plain,
% 0.34/0.60      (![X0 : $i]:
% 0.34/0.60         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.34/0.60          | ~ (l1_pre_topc @ X0)
% 0.34/0.60          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.34/0.60      inference('sup-', [status(thm)], ['45', '46'])).
% 0.34/0.60  thf('48', plain,
% 0.34/0.60      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.34/0.60      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.34/0.60  thf('49', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.34/0.60      inference('demod', [status(thm)], ['0', '3'])).
% 0.34/0.60  thf('50', plain,
% 0.34/0.60      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.34/0.60      inference('sup-', [status(thm)], ['48', '49'])).
% 0.34/0.60  thf('51', plain,
% 0.34/0.60      ((((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))
% 0.34/0.60        | ~ (l1_pre_topc @ sk_A)
% 0.34/0.60        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.34/0.60      inference('sup-', [status(thm)], ['47', '50'])).
% 0.34/0.60  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.60  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.34/0.60      inference('demod', [status(thm)], ['39', '40'])).
% 0.34/0.60  thf('54', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.34/0.60      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.34/0.60  thf('55', plain,
% 0.34/0.60      (((v2_tex_2 @ k1_xboole_0 @ sk_A) | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.34/0.60      inference('demod', [status(thm)], ['38', '41', '42', '54'])).
% 0.34/0.60  thf('56', plain, ((v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.34/0.60      inference('simplify', [status(thm)], ['55'])).
% 0.34/0.60  thf('57', plain, ($false), inference('demod', [status(thm)], ['4', '56'])).
% 0.34/0.60  
% 0.34/0.60  % SZS output end Refutation
% 0.34/0.60  
% 0.34/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
