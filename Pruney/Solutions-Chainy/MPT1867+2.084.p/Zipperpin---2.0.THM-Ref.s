%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8rcop4lsR6

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:37 EST 2020

% Result     : Theorem 1.97s
% Output     : Refutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 141 expanded)
%              Number of leaves         :   30 (  55 expanded)
%              Depth                    :   15
%              Number of atoms          :  573 (1098 expanded)
%              Number of equality atoms :   42 (  58 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_xboole_0 @ sk_B_1 ),
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
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('7',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

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

thf('9',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( r1_tarski @ ( sk_C @ X21 @ X22 ) @ X21 )
      | ( v2_tex_2 @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ X1 @ X0 )
      | ( r1_tarski @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('15',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('18',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( sk_C @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['13','14'])).

thf('23',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','23'])).

thf(rc6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('25',plain,(
    ! [X20: $i] :
      ( ( v4_pre_topc @ ( sk_B @ X20 ) @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[rc6_pre_topc])).

thf('26',plain,(
    ! [X20: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[rc6_pre_topc])).

thf('27',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('28',plain,(
    ! [X21: $i,X22: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v4_pre_topc @ X24 @ X22 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X22 ) @ X21 @ X24 )
       != ( sk_C @ X21 @ X22 ) )
      | ( v2_tex_2 @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ X1 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v4_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('31',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X10 @ X12 @ X11 )
        = ( k9_subset_1 @ X10 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k9_subset_1 @ X0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('34',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k9_subset_1 @ X15 @ X13 @ X14 )
        = ( k3_xboole_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('36',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('37',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('40',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('42',plain,(
    ! [X1: $i,X3: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k9_subset_1 @ X0 @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['32','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v4_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['29','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v4_pre_topc @ ( sk_B @ X0 ) @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v4_pre_topc @ ( sk_B @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','51'])).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['13','14'])).

thf('54',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['52','53','54','55'])).

thf('57',plain,(
    v2_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['4','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8rcop4lsR6
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 12:23:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 1.97/2.19  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.97/2.19  % Solved by: fo/fo7.sh
% 1.97/2.19  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.97/2.19  % done 2261 iterations in 1.707s
% 1.97/2.19  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.97/2.19  % SZS output start Refutation
% 1.97/2.19  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.97/2.19  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.97/2.19  thf(sk_B_type, type, sk_B: $i > $i).
% 1.97/2.19  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.97/2.19  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.97/2.19  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.97/2.19  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.97/2.19  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 1.97/2.19  thf(sk_A_type, type, sk_A: $i).
% 1.97/2.19  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.97/2.19  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 1.97/2.19  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.97/2.19  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.97/2.19  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.97/2.19  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.97/2.19  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.97/2.19  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.97/2.19  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.97/2.19  thf(t35_tex_2, conjecture,
% 1.97/2.19    (![A:$i]:
% 1.97/2.19     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.97/2.19       ( ![B:$i]:
% 1.97/2.19         ( ( ( v1_xboole_0 @ B ) & 
% 1.97/2.19             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.97/2.19           ( v2_tex_2 @ B @ A ) ) ) ))).
% 1.97/2.19  thf(zf_stmt_0, negated_conjecture,
% 1.97/2.19    (~( ![A:$i]:
% 1.97/2.19        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.97/2.19            ( l1_pre_topc @ A ) ) =>
% 1.97/2.19          ( ![B:$i]:
% 1.97/2.19            ( ( ( v1_xboole_0 @ B ) & 
% 1.97/2.19                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.97/2.19              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 1.97/2.19    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 1.97/2.19  thf('0', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf('1', plain, ((v1_xboole_0 @ sk_B_1)),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf(l13_xboole_0, axiom,
% 1.97/2.19    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.97/2.19  thf('2', plain,
% 1.97/2.19      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.97/2.19      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.97/2.19  thf('3', plain, (((sk_B_1) = (k1_xboole_0))),
% 1.97/2.19      inference('sup-', [status(thm)], ['1', '2'])).
% 1.97/2.19  thf('4', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 1.97/2.19      inference('demod', [status(thm)], ['0', '3'])).
% 1.97/2.19  thf('5', plain,
% 1.97/2.19      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.97/2.19      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.97/2.19  thf('6', plain,
% 1.97/2.19      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.97/2.19      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.97/2.19  thf(t4_subset_1, axiom,
% 1.97/2.19    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.97/2.19  thf('7', plain,
% 1.97/2.19      (![X16 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 1.97/2.19      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.97/2.19  thf('8', plain,
% 1.97/2.19      (![X0 : $i, X1 : $i]:
% 1.97/2.19         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 1.97/2.19      inference('sup+', [status(thm)], ['6', '7'])).
% 1.97/2.19  thf(d6_tex_2, axiom,
% 1.97/2.19    (![A:$i]:
% 1.97/2.19     ( ( l1_pre_topc @ A ) =>
% 1.97/2.19       ( ![B:$i]:
% 1.97/2.19         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.97/2.19           ( ( v2_tex_2 @ B @ A ) <=>
% 1.97/2.19             ( ![C:$i]:
% 1.97/2.19               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.97/2.19                 ( ~( ( r1_tarski @ C @ B ) & 
% 1.97/2.19                      ( ![D:$i]:
% 1.97/2.19                        ( ( m1_subset_1 @
% 1.97/2.19                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.97/2.19                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 1.97/2.19                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 1.97/2.19                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.97/2.19  thf('9', plain,
% 1.97/2.19      (![X21 : $i, X22 : $i]:
% 1.97/2.19         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.97/2.19          | (r1_tarski @ (sk_C @ X21 @ X22) @ X21)
% 1.97/2.19          | (v2_tex_2 @ X21 @ X22)
% 1.97/2.19          | ~ (l1_pre_topc @ X22))),
% 1.97/2.19      inference('cnf', [status(esa)], [d6_tex_2])).
% 1.97/2.19  thf('10', plain,
% 1.97/2.19      (![X0 : $i, X1 : $i]:
% 1.97/2.19         (~ (v1_xboole_0 @ X1)
% 1.97/2.19          | ~ (l1_pre_topc @ X0)
% 1.97/2.19          | (v2_tex_2 @ X1 @ X0)
% 1.97/2.19          | (r1_tarski @ (sk_C @ X1 @ X0) @ X1))),
% 1.97/2.19      inference('sup-', [status(thm)], ['8', '9'])).
% 1.97/2.19  thf(t3_xboole_1, axiom,
% 1.97/2.19    (![A:$i]:
% 1.97/2.19     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.97/2.19  thf('11', plain,
% 1.97/2.19      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ k1_xboole_0))),
% 1.97/2.19      inference('cnf', [status(esa)], [t3_xboole_1])).
% 1.97/2.19  thf('12', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 1.97/2.19          | ~ (l1_pre_topc @ X0)
% 1.97/2.19          | ~ (v1_xboole_0 @ k1_xboole_0)
% 1.97/2.19          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 1.97/2.19      inference('sup-', [status(thm)], ['10', '11'])).
% 1.97/2.19  thf('13', plain, ((v1_xboole_0 @ sk_B_1)),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf('14', plain, (((sk_B_1) = (k1_xboole_0))),
% 1.97/2.19      inference('sup-', [status(thm)], ['1', '2'])).
% 1.97/2.19  thf('15', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.97/2.19      inference('demod', [status(thm)], ['13', '14'])).
% 1.97/2.19  thf('16', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 1.97/2.19          | ~ (l1_pre_topc @ X0)
% 1.97/2.19          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 1.97/2.19      inference('demod', [status(thm)], ['12', '15'])).
% 1.97/2.19  thf('17', plain,
% 1.97/2.19      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.97/2.19      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.97/2.19  thf('18', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 1.97/2.19      inference('demod', [status(thm)], ['0', '3'])).
% 1.97/2.19  thf('19', plain,
% 1.97/2.19      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 1.97/2.19      inference('sup-', [status(thm)], ['17', '18'])).
% 1.97/2.19  thf('20', plain,
% 1.97/2.19      ((((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))
% 1.97/2.19        | ~ (l1_pre_topc @ sk_A)
% 1.97/2.19        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.97/2.19      inference('sup-', [status(thm)], ['16', '19'])).
% 1.97/2.19  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf('22', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.97/2.19      inference('demod', [status(thm)], ['13', '14'])).
% 1.97/2.19  thf('23', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 1.97/2.19      inference('demod', [status(thm)], ['20', '21', '22'])).
% 1.97/2.19  thf('24', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         (((sk_C @ X0 @ sk_A) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.97/2.19      inference('sup+', [status(thm)], ['5', '23'])).
% 1.97/2.19  thf(rc6_pre_topc, axiom,
% 1.97/2.19    (![A:$i]:
% 1.97/2.19     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.97/2.19       ( ?[B:$i]:
% 1.97/2.19         ( ( v4_pre_topc @ B @ A ) & 
% 1.97/2.19           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 1.97/2.19  thf('25', plain,
% 1.97/2.19      (![X20 : $i]:
% 1.97/2.19         ((v4_pre_topc @ (sk_B @ X20) @ X20)
% 1.97/2.19          | ~ (l1_pre_topc @ X20)
% 1.97/2.19          | ~ (v2_pre_topc @ X20))),
% 1.97/2.19      inference('cnf', [status(esa)], [rc6_pre_topc])).
% 1.97/2.19  thf('26', plain,
% 1.97/2.19      (![X20 : $i]:
% 1.97/2.19         ((m1_subset_1 @ (sk_B @ X20) @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 1.97/2.19          | ~ (l1_pre_topc @ X20)
% 1.97/2.19          | ~ (v2_pre_topc @ X20))),
% 1.97/2.19      inference('cnf', [status(esa)], [rc6_pre_topc])).
% 1.97/2.19  thf('27', plain,
% 1.97/2.19      (![X16 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 1.97/2.19      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.97/2.19  thf('28', plain,
% 1.97/2.19      (![X21 : $i, X22 : $i, X24 : $i]:
% 1.97/2.19         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.97/2.19          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.97/2.19          | ~ (v4_pre_topc @ X24 @ X22)
% 1.97/2.19          | ((k9_subset_1 @ (u1_struct_0 @ X22) @ X21 @ X24)
% 1.97/2.19              != (sk_C @ X21 @ X22))
% 1.97/2.19          | (v2_tex_2 @ X21 @ X22)
% 1.97/2.19          | ~ (l1_pre_topc @ X22))),
% 1.97/2.19      inference('cnf', [status(esa)], [d6_tex_2])).
% 1.97/2.19  thf('29', plain,
% 1.97/2.19      (![X0 : $i, X1 : $i]:
% 1.97/2.19         (~ (l1_pre_topc @ X0)
% 1.97/2.19          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 1.97/2.19          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 1.97/2.19              != (sk_C @ k1_xboole_0 @ X0))
% 1.97/2.19          | ~ (v4_pre_topc @ X1 @ X0)
% 1.97/2.19          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.97/2.19      inference('sup-', [status(thm)], ['27', '28'])).
% 1.97/2.19  thf('30', plain,
% 1.97/2.19      (![X16 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 1.97/2.19      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.97/2.19  thf(commutativity_k9_subset_1, axiom,
% 1.97/2.19    (![A:$i,B:$i,C:$i]:
% 1.97/2.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.97/2.19       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 1.97/2.19  thf('31', plain,
% 1.97/2.19      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.97/2.19         (((k9_subset_1 @ X10 @ X12 @ X11) = (k9_subset_1 @ X10 @ X11 @ X12))
% 1.97/2.19          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 1.97/2.19      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 1.97/2.19  thf('32', plain,
% 1.97/2.19      (![X0 : $i, X1 : $i]:
% 1.97/2.19         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 1.97/2.19           = (k9_subset_1 @ X0 @ k1_xboole_0 @ X1))),
% 1.97/2.19      inference('sup-', [status(thm)], ['30', '31'])).
% 1.97/2.19  thf('33', plain,
% 1.97/2.19      (![X16 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 1.97/2.19      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.97/2.19  thf(redefinition_k9_subset_1, axiom,
% 1.97/2.19    (![A:$i,B:$i,C:$i]:
% 1.97/2.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.97/2.19       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 1.97/2.19  thf('34', plain,
% 1.97/2.19      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.97/2.19         (((k9_subset_1 @ X15 @ X13 @ X14) = (k3_xboole_0 @ X13 @ X14))
% 1.97/2.19          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 1.97/2.19      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 1.97/2.19  thf('35', plain,
% 1.97/2.19      (![X0 : $i, X1 : $i]:
% 1.97/2.19         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 1.97/2.19           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 1.97/2.19      inference('sup-', [status(thm)], ['33', '34'])).
% 1.97/2.19  thf(t3_boole, axiom,
% 1.97/2.19    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.97/2.19  thf('36', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 1.97/2.19      inference('cnf', [status(esa)], [t3_boole])).
% 1.97/2.19  thf(t48_xboole_1, axiom,
% 1.97/2.19    (![A:$i,B:$i]:
% 1.97/2.19     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.97/2.19  thf('37', plain,
% 1.97/2.19      (![X8 : $i, X9 : $i]:
% 1.97/2.19         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 1.97/2.19           = (k3_xboole_0 @ X8 @ X9))),
% 1.97/2.19      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.97/2.19  thf('38', plain,
% 1.97/2.19      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.97/2.19      inference('sup+', [status(thm)], ['36', '37'])).
% 1.97/2.19  thf('39', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 1.97/2.19      inference('cnf', [status(esa)], [t3_boole])).
% 1.97/2.19  thf(t36_xboole_1, axiom,
% 1.97/2.19    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.97/2.19  thf('40', plain,
% 1.97/2.19      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 1.97/2.19      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.97/2.19  thf('41', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.97/2.19      inference('sup+', [status(thm)], ['39', '40'])).
% 1.97/2.19  thf(l32_xboole_1, axiom,
% 1.97/2.19    (![A:$i,B:$i]:
% 1.97/2.19     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.97/2.19  thf('42', plain,
% 1.97/2.19      (![X1 : $i, X3 : $i]:
% 1.97/2.19         (((k4_xboole_0 @ X1 @ X3) = (k1_xboole_0)) | ~ (r1_tarski @ X1 @ X3))),
% 1.97/2.19      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.97/2.19  thf('43', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.97/2.19      inference('sup-', [status(thm)], ['41', '42'])).
% 1.97/2.19  thf('44', plain,
% 1.97/2.19      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.97/2.19      inference('demod', [status(thm)], ['38', '43'])).
% 1.97/2.19  thf('45', plain,
% 1.97/2.19      (![X0 : $i, X1 : $i]:
% 1.97/2.19         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.97/2.19      inference('demod', [status(thm)], ['35', '44'])).
% 1.97/2.19  thf('46', plain,
% 1.97/2.19      (![X0 : $i, X1 : $i]:
% 1.97/2.19         ((k1_xboole_0) = (k9_subset_1 @ X0 @ k1_xboole_0 @ X1))),
% 1.97/2.19      inference('demod', [status(thm)], ['32', '45'])).
% 1.97/2.19  thf('47', plain,
% 1.97/2.19      (![X0 : $i, X1 : $i]:
% 1.97/2.19         (~ (l1_pre_topc @ X0)
% 1.97/2.19          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 1.97/2.19          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 1.97/2.19          | ~ (v4_pre_topc @ X1 @ X0)
% 1.97/2.19          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.97/2.19      inference('demod', [status(thm)], ['29', '46'])).
% 1.97/2.19  thf('48', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         (~ (v2_pre_topc @ X0)
% 1.97/2.19          | ~ (l1_pre_topc @ X0)
% 1.97/2.19          | ~ (v4_pre_topc @ (sk_B @ X0) @ X0)
% 1.97/2.19          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 1.97/2.19          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 1.97/2.19          | ~ (l1_pre_topc @ X0))),
% 1.97/2.19      inference('sup-', [status(thm)], ['26', '47'])).
% 1.97/2.19  thf('49', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 1.97/2.19          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 1.97/2.19          | ~ (v4_pre_topc @ (sk_B @ X0) @ X0)
% 1.97/2.19          | ~ (l1_pre_topc @ X0)
% 1.97/2.19          | ~ (v2_pre_topc @ X0))),
% 1.97/2.19      inference('simplify', [status(thm)], ['48'])).
% 1.97/2.19  thf('50', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         (~ (v2_pre_topc @ X0)
% 1.97/2.19          | ~ (l1_pre_topc @ X0)
% 1.97/2.19          | ~ (v2_pre_topc @ X0)
% 1.97/2.19          | ~ (l1_pre_topc @ X0)
% 1.97/2.19          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 1.97/2.19          | (v2_tex_2 @ k1_xboole_0 @ X0))),
% 1.97/2.19      inference('sup-', [status(thm)], ['25', '49'])).
% 1.97/2.19  thf('51', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 1.97/2.19          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 1.97/2.19          | ~ (l1_pre_topc @ X0)
% 1.97/2.19          | ~ (v2_pre_topc @ X0))),
% 1.97/2.19      inference('simplify', [status(thm)], ['50'])).
% 1.97/2.19  thf('52', plain,
% 1.97/2.19      ((((k1_xboole_0) != (k1_xboole_0))
% 1.97/2.19        | ~ (v1_xboole_0 @ k1_xboole_0)
% 1.97/2.19        | ~ (v2_pre_topc @ sk_A)
% 1.97/2.19        | ~ (l1_pre_topc @ sk_A)
% 1.97/2.19        | (v2_tex_2 @ k1_xboole_0 @ sk_A))),
% 1.97/2.19      inference('sup-', [status(thm)], ['24', '51'])).
% 1.97/2.19  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.97/2.19      inference('demod', [status(thm)], ['13', '14'])).
% 1.97/2.19  thf('54', plain, ((v2_pre_topc @ sk_A)),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf('56', plain,
% 1.97/2.19      ((((k1_xboole_0) != (k1_xboole_0)) | (v2_tex_2 @ k1_xboole_0 @ sk_A))),
% 1.97/2.19      inference('demod', [status(thm)], ['52', '53', '54', '55'])).
% 1.97/2.19  thf('57', plain, ((v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 1.97/2.19      inference('simplify', [status(thm)], ['56'])).
% 1.97/2.19  thf('58', plain, ($false), inference('demod', [status(thm)], ['4', '57'])).
% 1.97/2.19  
% 1.97/2.19  % SZS output end Refutation
% 1.97/2.19  
% 1.97/2.20  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
