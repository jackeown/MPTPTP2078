%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AtiLanqaGp

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:33 EST 2020

% Result     : Theorem 1.95s
% Output     : Refutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 196 expanded)
%              Number of leaves         :   26 (  69 expanded)
%              Depth                    :   13
%              Number of atoms          :  577 (1579 expanded)
%              Number of equality atoms :   43 (  86 expanded)
%              Maximal formula depth    :   19 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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
    v1_xboole_0 @ sk_B_1 ),
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
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('7',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('9',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

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

thf('11',plain,(
    ! [X23: $i,X24: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v4_pre_topc @ X26 @ X24 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X24 ) @ X23 @ X26 )
       != ( sk_C @ X23 @ X24 ) )
      | ( v2_tex_2 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ X1 )
       != ( sk_C @ X0 @ sk_A ) )
      | ~ ( v4_pre_topc @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ X1 )
       != ( sk_C @ X0 @ sk_A ) )
      | ~ ( v4_pre_topc @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ k1_xboole_0 @ sk_A )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ k1_xboole_0 )
       != ( sk_C @ X0 @ sk_A ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('17',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v4_pre_topc @ X21 @ X22 )
      | ~ ( v1_xboole_0 @ X21 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('18',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v4_pre_topc @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['0','3'])).

thf('22',plain,(
    v4_pre_topc @ k1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['18','19','20','21'])).

thf('23',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k9_subset_1 @ X14 @ X12 @ X13 )
        = ( k3_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('27',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['26'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('28',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('30',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('31',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['26'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('35',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('39',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( sk_C @ X0 @ sk_A ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','22','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('43',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('44',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( r1_tarski @ ( sk_C @ X23 @ X24 ) @ X23 )
      | ( v2_tex_2 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('45',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( r1_tarski @ ( sk_C @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( r1_tarski @ ( sk_C @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('50',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    r1_tarski @ ( sk_C @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 ),
    inference(clc,[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('53',plain,
    ( ( k4_xboole_0 @ ( sk_C @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('55',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['53','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_tex_2 @ X0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['41','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('63',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ X0 ) ),
    inference(clc,[status(thm)],['61','64'])).

thf('66',plain,(
    $false ),
    inference('sup-',[status(thm)],['4','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AtiLanqaGp
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:19:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.95/2.13  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.95/2.13  % Solved by: fo/fo7.sh
% 1.95/2.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.95/2.13  % done 3576 iterations in 1.680s
% 1.95/2.13  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.95/2.13  % SZS output start Refutation
% 1.95/2.13  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.95/2.13  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.95/2.13  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 1.95/2.13  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.95/2.13  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.95/2.13  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.95/2.13  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 1.95/2.13  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.95/2.13  thf(sk_A_type, type, sk_A: $i).
% 1.95/2.13  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.95/2.13  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.95/2.13  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.95/2.13  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.95/2.13  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.95/2.13  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.95/2.13  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.95/2.13  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.95/2.13  thf(t35_tex_2, conjecture,
% 1.95/2.13    (![A:$i]:
% 1.95/2.13     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.95/2.13       ( ![B:$i]:
% 1.95/2.13         ( ( ( v1_xboole_0 @ B ) & 
% 1.95/2.13             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.95/2.13           ( v2_tex_2 @ B @ A ) ) ) ))).
% 1.95/2.13  thf(zf_stmt_0, negated_conjecture,
% 1.95/2.13    (~( ![A:$i]:
% 1.95/2.13        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.95/2.13            ( l1_pre_topc @ A ) ) =>
% 1.95/2.13          ( ![B:$i]:
% 1.95/2.13            ( ( ( v1_xboole_0 @ B ) & 
% 1.95/2.13                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.95/2.13              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 1.95/2.13    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 1.95/2.13  thf('0', plain, ((v1_xboole_0 @ sk_B_1)),
% 1.95/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.13  thf('1', plain, ((v1_xboole_0 @ sk_B_1)),
% 1.95/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.13  thf(l13_xboole_0, axiom,
% 1.95/2.13    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.95/2.13  thf('2', plain,
% 1.95/2.13      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.95/2.13      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.95/2.13  thf('3', plain, (((sk_B_1) = (k1_xboole_0))),
% 1.95/2.13      inference('sup-', [status(thm)], ['1', '2'])).
% 1.95/2.13  thf('4', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.95/2.13      inference('demod', [status(thm)], ['0', '3'])).
% 1.95/2.13  thf('5', plain,
% 1.95/2.13      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.95/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.13  thf('6', plain, (((sk_B_1) = (k1_xboole_0))),
% 1.95/2.13      inference('sup-', [status(thm)], ['1', '2'])).
% 1.95/2.13  thf('7', plain,
% 1.95/2.13      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.95/2.13      inference('demod', [status(thm)], ['5', '6'])).
% 1.95/2.13  thf('8', plain,
% 1.95/2.13      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.95/2.13      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.95/2.13  thf('9', plain,
% 1.95/2.13      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.95/2.13      inference('demod', [status(thm)], ['5', '6'])).
% 1.95/2.13  thf('10', plain,
% 1.95/2.13      (![X0 : $i]:
% 1.95/2.13         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.95/2.13          | ~ (v1_xboole_0 @ X0))),
% 1.95/2.13      inference('sup+', [status(thm)], ['8', '9'])).
% 1.95/2.13  thf(d6_tex_2, axiom,
% 1.95/2.13    (![A:$i]:
% 1.95/2.13     ( ( l1_pre_topc @ A ) =>
% 1.95/2.13       ( ![B:$i]:
% 1.95/2.13         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.95/2.13           ( ( v2_tex_2 @ B @ A ) <=>
% 1.95/2.13             ( ![C:$i]:
% 1.95/2.13               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.95/2.13                 ( ~( ( r1_tarski @ C @ B ) & 
% 1.95/2.13                      ( ![D:$i]:
% 1.95/2.13                        ( ( m1_subset_1 @
% 1.95/2.13                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.95/2.13                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 1.95/2.13                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 1.95/2.13                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.95/2.13  thf('11', plain,
% 1.95/2.13      (![X23 : $i, X24 : $i, X26 : $i]:
% 1.95/2.13         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 1.95/2.13          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 1.95/2.13          | ~ (v4_pre_topc @ X26 @ X24)
% 1.95/2.13          | ((k9_subset_1 @ (u1_struct_0 @ X24) @ X23 @ X26)
% 1.95/2.13              != (sk_C @ X23 @ X24))
% 1.95/2.13          | (v2_tex_2 @ X23 @ X24)
% 1.95/2.13          | ~ (l1_pre_topc @ X24))),
% 1.95/2.13      inference('cnf', [status(esa)], [d6_tex_2])).
% 1.95/2.13  thf('12', plain,
% 1.95/2.13      (![X0 : $i, X1 : $i]:
% 1.95/2.13         (~ (v1_xboole_0 @ X0)
% 1.95/2.13          | ~ (l1_pre_topc @ sk_A)
% 1.95/2.13          | (v2_tex_2 @ X0 @ sk_A)
% 1.95/2.13          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ X1)
% 1.95/2.13              != (sk_C @ X0 @ sk_A))
% 1.95/2.13          | ~ (v4_pre_topc @ X1 @ sk_A)
% 1.95/2.13          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.95/2.13      inference('sup-', [status(thm)], ['10', '11'])).
% 1.95/2.13  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.13  thf('14', plain,
% 1.95/2.13      (![X0 : $i, X1 : $i]:
% 1.95/2.13         (~ (v1_xboole_0 @ X0)
% 1.95/2.13          | (v2_tex_2 @ X0 @ sk_A)
% 1.95/2.13          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ X1)
% 1.95/2.13              != (sk_C @ X0 @ sk_A))
% 1.95/2.13          | ~ (v4_pre_topc @ X1 @ sk_A)
% 1.95/2.13          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.95/2.13      inference('demod', [status(thm)], ['12', '13'])).
% 1.95/2.13  thf('15', plain,
% 1.95/2.13      (![X0 : $i]:
% 1.95/2.13         (~ (v4_pre_topc @ k1_xboole_0 @ sk_A)
% 1.95/2.13          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ k1_xboole_0)
% 1.95/2.13              != (sk_C @ X0 @ sk_A))
% 1.95/2.13          | (v2_tex_2 @ X0 @ sk_A)
% 1.95/2.13          | ~ (v1_xboole_0 @ X0))),
% 1.95/2.13      inference('sup-', [status(thm)], ['7', '14'])).
% 1.95/2.13  thf('16', plain,
% 1.95/2.13      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.95/2.13      inference('demod', [status(thm)], ['5', '6'])).
% 1.95/2.13  thf(cc2_pre_topc, axiom,
% 1.95/2.13    (![A:$i]:
% 1.95/2.13     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.95/2.13       ( ![B:$i]:
% 1.95/2.13         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.95/2.13           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 1.95/2.13  thf('17', plain,
% 1.95/2.13      (![X21 : $i, X22 : $i]:
% 1.95/2.13         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.95/2.13          | (v4_pre_topc @ X21 @ X22)
% 1.95/2.13          | ~ (v1_xboole_0 @ X21)
% 1.95/2.13          | ~ (l1_pre_topc @ X22)
% 1.95/2.13          | ~ (v2_pre_topc @ X22))),
% 1.95/2.13      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 1.95/2.13  thf('18', plain,
% 1.95/2.13      ((~ (v2_pre_topc @ sk_A)
% 1.95/2.13        | ~ (l1_pre_topc @ sk_A)
% 1.95/2.13        | ~ (v1_xboole_0 @ k1_xboole_0)
% 1.95/2.13        | (v4_pre_topc @ k1_xboole_0 @ sk_A))),
% 1.95/2.13      inference('sup-', [status(thm)], ['16', '17'])).
% 1.95/2.13  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 1.95/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.13  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.13  thf('21', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.95/2.13      inference('demod', [status(thm)], ['0', '3'])).
% 1.95/2.13  thf('22', plain, ((v4_pre_topc @ k1_xboole_0 @ sk_A)),
% 1.95/2.13      inference('demod', [status(thm)], ['18', '19', '20', '21'])).
% 1.95/2.13  thf('23', plain,
% 1.95/2.13      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.95/2.13      inference('demod', [status(thm)], ['5', '6'])).
% 1.95/2.13  thf(redefinition_k9_subset_1, axiom,
% 1.95/2.13    (![A:$i,B:$i,C:$i]:
% 1.95/2.13     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.95/2.13       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 1.95/2.13  thf('24', plain,
% 1.95/2.13      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.95/2.13         (((k9_subset_1 @ X14 @ X12 @ X13) = (k3_xboole_0 @ X12 @ X13))
% 1.95/2.13          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 1.95/2.13      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 1.95/2.13  thf('25', plain,
% 1.95/2.13      (![X0 : $i]:
% 1.95/2.13         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ k1_xboole_0)
% 1.95/2.13           = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.95/2.13      inference('sup-', [status(thm)], ['23', '24'])).
% 1.95/2.13  thf(d10_xboole_0, axiom,
% 1.95/2.13    (![A:$i,B:$i]:
% 1.95/2.13     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.95/2.13  thf('26', plain,
% 1.95/2.13      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 1.95/2.13      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.95/2.13  thf('27', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 1.95/2.13      inference('simplify', [status(thm)], ['26'])).
% 1.95/2.13  thf(l32_xboole_1, axiom,
% 1.95/2.13    (![A:$i,B:$i]:
% 1.95/2.13     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.95/2.13  thf('28', plain,
% 1.95/2.13      (![X5 : $i, X7 : $i]:
% 1.95/2.13         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 1.95/2.13      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.95/2.13  thf('29', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.95/2.13      inference('sup-', [status(thm)], ['27', '28'])).
% 1.95/2.13  thf(t48_xboole_1, axiom,
% 1.95/2.13    (![A:$i,B:$i]:
% 1.95/2.13     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.95/2.13  thf('30', plain,
% 1.95/2.13      (![X10 : $i, X11 : $i]:
% 1.95/2.13         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 1.95/2.13           = (k3_xboole_0 @ X10 @ X11))),
% 1.95/2.13      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.95/2.13  thf('31', plain,
% 1.95/2.13      (![X10 : $i, X11 : $i]:
% 1.95/2.13         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 1.95/2.13           = (k3_xboole_0 @ X10 @ X11))),
% 1.95/2.13      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.95/2.13  thf('32', plain,
% 1.95/2.13      (![X0 : $i, X1 : $i]:
% 1.95/2.13         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.95/2.13           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.95/2.13      inference('sup+', [status(thm)], ['30', '31'])).
% 1.95/2.13  thf('33', plain,
% 1.95/2.13      (![X0 : $i]:
% 1.95/2.13         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0))
% 1.95/2.13           = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.95/2.13      inference('sup+', [status(thm)], ['29', '32'])).
% 1.95/2.13  thf('34', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 1.95/2.13      inference('simplify', [status(thm)], ['26'])).
% 1.95/2.13  thf(t28_xboole_1, axiom,
% 1.95/2.13    (![A:$i,B:$i]:
% 1.95/2.13     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.95/2.13  thf('35', plain,
% 1.95/2.13      (![X8 : $i, X9 : $i]:
% 1.95/2.13         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 1.95/2.13      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.95/2.13  thf('36', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.95/2.13      inference('sup-', [status(thm)], ['34', '35'])).
% 1.95/2.13  thf('37', plain,
% 1.95/2.13      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.95/2.13      inference('demod', [status(thm)], ['33', '36'])).
% 1.95/2.13  thf('38', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.95/2.13      inference('sup-', [status(thm)], ['27', '28'])).
% 1.95/2.13  thf('39', plain,
% 1.95/2.13      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.95/2.13      inference('demod', [status(thm)], ['37', '38'])).
% 1.95/2.13  thf('40', plain,
% 1.95/2.13      (![X0 : $i]:
% 1.95/2.13         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ k1_xboole_0)
% 1.95/2.13           = (k1_xboole_0))),
% 1.95/2.13      inference('demod', [status(thm)], ['25', '39'])).
% 1.95/2.13  thf('41', plain,
% 1.95/2.13      (![X0 : $i]:
% 1.95/2.13         (((k1_xboole_0) != (sk_C @ X0 @ sk_A))
% 1.95/2.13          | (v2_tex_2 @ X0 @ sk_A)
% 1.95/2.13          | ~ (v1_xboole_0 @ X0))),
% 1.95/2.13      inference('demod', [status(thm)], ['15', '22', '40'])).
% 1.95/2.13  thf('42', plain,
% 1.95/2.13      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.95/2.13      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.95/2.13  thf('43', plain,
% 1.95/2.13      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.95/2.13      inference('demod', [status(thm)], ['5', '6'])).
% 1.95/2.13  thf('44', plain,
% 1.95/2.13      (![X23 : $i, X24 : $i]:
% 1.95/2.13         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 1.95/2.13          | (r1_tarski @ (sk_C @ X23 @ X24) @ X23)
% 1.95/2.13          | (v2_tex_2 @ X23 @ X24)
% 1.95/2.13          | ~ (l1_pre_topc @ X24))),
% 1.95/2.13      inference('cnf', [status(esa)], [d6_tex_2])).
% 1.95/2.13  thf('45', plain,
% 1.95/2.13      ((~ (l1_pre_topc @ sk_A)
% 1.95/2.13        | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 1.95/2.13        | (r1_tarski @ (sk_C @ k1_xboole_0 @ sk_A) @ k1_xboole_0))),
% 1.95/2.13      inference('sup-', [status(thm)], ['43', '44'])).
% 1.95/2.13  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.13  thf('47', plain,
% 1.95/2.13      (((v2_tex_2 @ k1_xboole_0 @ sk_A)
% 1.95/2.13        | (r1_tarski @ (sk_C @ k1_xboole_0 @ sk_A) @ k1_xboole_0))),
% 1.95/2.13      inference('demod', [status(thm)], ['45', '46'])).
% 1.95/2.13  thf('48', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 1.95/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.13  thf('49', plain, (((sk_B_1) = (k1_xboole_0))),
% 1.95/2.13      inference('sup-', [status(thm)], ['1', '2'])).
% 1.95/2.13  thf('50', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 1.95/2.13      inference('demod', [status(thm)], ['48', '49'])).
% 1.95/2.13  thf('51', plain, ((r1_tarski @ (sk_C @ k1_xboole_0 @ sk_A) @ k1_xboole_0)),
% 1.95/2.13      inference('clc', [status(thm)], ['47', '50'])).
% 1.95/2.13  thf('52', plain,
% 1.95/2.13      (![X5 : $i, X7 : $i]:
% 1.95/2.13         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 1.95/2.13      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.95/2.13  thf('53', plain,
% 1.95/2.13      (((k4_xboole_0 @ (sk_C @ k1_xboole_0 @ sk_A) @ k1_xboole_0)
% 1.95/2.13         = (k1_xboole_0))),
% 1.95/2.13      inference('sup-', [status(thm)], ['51', '52'])).
% 1.95/2.13  thf('54', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.95/2.13      inference('sup-', [status(thm)], ['27', '28'])).
% 1.95/2.13  thf('55', plain,
% 1.95/2.13      (![X10 : $i, X11 : $i]:
% 1.95/2.13         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 1.95/2.13           = (k3_xboole_0 @ X10 @ X11))),
% 1.95/2.13      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.95/2.13  thf('56', plain,
% 1.95/2.13      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 1.95/2.13      inference('sup+', [status(thm)], ['54', '55'])).
% 1.95/2.13  thf('57', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.95/2.13      inference('sup-', [status(thm)], ['34', '35'])).
% 1.95/2.13  thf('58', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.95/2.13      inference('demod', [status(thm)], ['56', '57'])).
% 1.95/2.13  thf('59', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 1.95/2.13      inference('demod', [status(thm)], ['53', '58'])).
% 1.95/2.13  thf('60', plain,
% 1.95/2.13      (![X0 : $i]:
% 1.95/2.13         (((sk_C @ X0 @ sk_A) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.95/2.13      inference('sup+', [status(thm)], ['42', '59'])).
% 1.95/2.13  thf('61', plain,
% 1.95/2.13      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v2_tex_2 @ X0 @ sk_A))),
% 1.95/2.13      inference('clc', [status(thm)], ['41', '60'])).
% 1.95/2.13  thf('62', plain,
% 1.95/2.13      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.95/2.13      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.95/2.13  thf('63', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 1.95/2.13      inference('demod', [status(thm)], ['48', '49'])).
% 1.95/2.13  thf('64', plain,
% 1.95/2.13      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 1.95/2.13      inference('sup-', [status(thm)], ['62', '63'])).
% 1.95/2.13  thf('65', plain, (![X0 : $i]: ~ (v1_xboole_0 @ X0)),
% 1.95/2.13      inference('clc', [status(thm)], ['61', '64'])).
% 1.95/2.13  thf('66', plain, ($false), inference('sup-', [status(thm)], ['4', '65'])).
% 1.95/2.13  
% 1.95/2.13  % SZS output end Refutation
% 1.95/2.13  
% 1.95/2.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
