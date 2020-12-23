%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2zj2pRKIUG

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:38 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 227 expanded)
%              Number of leaves         :   25 (  83 expanded)
%              Depth                    :   15
%              Number of atoms          :  555 (1785 expanded)
%              Number of equality atoms :   12 (  35 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(t66_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v3_tex_2 @ B @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v3_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ? [B: $i] :
            ( ( v3_tex_2 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_tex_2])).

thf('0',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X10 = X9 )
      | ( v1_subset_1 @ X10 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(cc4_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ~ ( v1_subset_1 @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( v1_subset_1 @ X4 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc4_subset_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf(t35_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v2_tex_2 @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t35_tex_2])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_tex_2 @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_tex_2 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','18'])).

thf('20',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_tex_2 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('24',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('28',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t65_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ~ ( ( v2_tex_2 @ B @ A )
              & ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ~ ( ( r1_tarski @ B @ C )
                      & ( v3_tex_2 @ C @ A ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v2_tex_2 @ X13 @ X14 )
      | ( m1_subset_1 @ ( sk_C @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v3_tdlat_3 @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_C @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_C @ k1_xboole_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','30'])).

thf('32',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( m1_subset_1 @ ( sk_C @ k1_xboole_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','33','34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ ( sk_C @ k1_xboole_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X15: $i] :
      ( ~ ( v3_tex_2 @ X15 @ sk_A )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ~ ( v3_tex_2 @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('46',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v2_tex_2 @ X13 @ X14 )
      | ( v3_tex_2 @ ( sk_C @ X13 @ X14 ) @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v3_tdlat_3 @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_tex_2 @ ( sk_C @ ( k3_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ ( k3_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( v3_tex_2 @ ( sk_C @ ( k3_xboole_0 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( v3_tex_2 @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['41','50'])).

thf('52',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v3_tex_2 @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['51','52','53','54','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v3_tex_2 @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['40','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2zj2pRKIUG
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:21:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.61/0.80  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.61/0.80  % Solved by: fo/fo7.sh
% 0.61/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.80  % done 667 iterations in 0.323s
% 0.61/0.80  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.61/0.80  % SZS output start Refutation
% 0.61/0.80  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.61/0.80  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.61/0.80  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.61/0.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.61/0.80  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.61/0.80  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.61/0.80  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.61/0.80  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.61/0.80  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.61/0.80  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.61/0.80  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.61/0.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.61/0.80  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.61/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.80  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.61/0.80  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.61/0.80  thf(t66_tex_2, conjecture,
% 0.61/0.80    (![A:$i]:
% 0.61/0.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.61/0.80         ( l1_pre_topc @ A ) ) =>
% 0.61/0.80       ( ?[B:$i]:
% 0.61/0.80         ( ( v3_tex_2 @ B @ A ) & 
% 0.61/0.80           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.61/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.61/0.80    (~( ![A:$i]:
% 0.61/0.80        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.61/0.80            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.61/0.80          ( ?[B:$i]:
% 0.61/0.80            ( ( v3_tex_2 @ B @ A ) & 
% 0.61/0.80              ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.61/0.80    inference('cnf.neg', [status(esa)], [t66_tex_2])).
% 0.61/0.80  thf('0', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.80  thf(t17_xboole_1, axiom,
% 0.61/0.80    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.61/0.80  thf('1', plain,
% 0.61/0.80      (![X2 : $i, X3 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ X2)),
% 0.61/0.80      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.61/0.80  thf(t3_subset, axiom,
% 0.61/0.80    (![A:$i,B:$i]:
% 0.61/0.80     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.61/0.80  thf('2', plain,
% 0.61/0.80      (![X6 : $i, X8 : $i]:
% 0.61/0.80         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.61/0.80      inference('cnf', [status(esa)], [t3_subset])).
% 0.61/0.80  thf('3', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.61/0.80      inference('sup-', [status(thm)], ['1', '2'])).
% 0.61/0.80  thf(d7_subset_1, axiom,
% 0.61/0.80    (![A:$i,B:$i]:
% 0.61/0.80     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.61/0.80       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.61/0.80  thf('4', plain,
% 0.61/0.80      (![X9 : $i, X10 : $i]:
% 0.61/0.80         (((X10) = (X9))
% 0.61/0.80          | (v1_subset_1 @ X10 @ X9)
% 0.61/0.80          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.61/0.80      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.61/0.80  thf('5', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((v1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 0.61/0.80          | ((k3_xboole_0 @ X0 @ X1) = (X0)))),
% 0.61/0.80      inference('sup-', [status(thm)], ['3', '4'])).
% 0.61/0.80  thf('6', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.61/0.80      inference('sup-', [status(thm)], ['1', '2'])).
% 0.61/0.80  thf(cc4_subset_1, axiom,
% 0.61/0.80    (![A:$i]:
% 0.61/0.80     ( ( v1_xboole_0 @ A ) =>
% 0.61/0.80       ( ![B:$i]:
% 0.61/0.80         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.61/0.80           ( ~( v1_subset_1 @ B @ A ) ) ) ) ))).
% 0.61/0.80  thf('7', plain,
% 0.61/0.80      (![X4 : $i, X5 : $i]:
% 0.61/0.80         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.61/0.80          | ~ (v1_subset_1 @ X4 @ X5)
% 0.61/0.80          | ~ (v1_xboole_0 @ X5))),
% 0.61/0.80      inference('cnf', [status(esa)], [cc4_subset_1])).
% 0.61/0.80  thf('8', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (~ (v1_xboole_0 @ X0) | ~ (v1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.61/0.80      inference('sup-', [status(thm)], ['6', '7'])).
% 0.61/0.80  thf('9', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.61/0.80      inference('sup-', [status(thm)], ['5', '8'])).
% 0.61/0.80  thf(commutativity_k3_xboole_0, axiom,
% 0.61/0.80    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.61/0.80  thf('10', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.61/0.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.61/0.80  thf('11', plain,
% 0.61/0.80      (![X2 : $i, X3 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ X2)),
% 0.61/0.80      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.61/0.80  thf('12', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.61/0.80      inference('sup+', [status(thm)], ['10', '11'])).
% 0.61/0.80  thf('13', plain,
% 0.61/0.80      (![X6 : $i, X8 : $i]:
% 0.61/0.80         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.61/0.80      inference('cnf', [status(esa)], [t3_subset])).
% 0.61/0.80  thf('14', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.61/0.80      inference('sup-', [status(thm)], ['12', '13'])).
% 0.61/0.80  thf('15', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.61/0.80      inference('sup+', [status(thm)], ['9', '14'])).
% 0.61/0.80  thf(t35_tex_2, axiom,
% 0.61/0.80    (![A:$i]:
% 0.61/0.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.61/0.80       ( ![B:$i]:
% 0.61/0.80         ( ( ( v1_xboole_0 @ B ) & 
% 0.61/0.80             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.61/0.80           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.61/0.80  thf('16', plain,
% 0.61/0.80      (![X11 : $i, X12 : $i]:
% 0.61/0.80         (~ (v1_xboole_0 @ X11)
% 0.61/0.80          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.61/0.80          | (v2_tex_2 @ X11 @ X12)
% 0.61/0.80          | ~ (l1_pre_topc @ X12)
% 0.61/0.80          | ~ (v2_pre_topc @ X12)
% 0.61/0.80          | (v2_struct_0 @ X12))),
% 0.61/0.80      inference('cnf', [status(esa)], [t35_tex_2])).
% 0.61/0.80  thf('17', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (~ (v1_xboole_0 @ X1)
% 0.61/0.80          | (v2_struct_0 @ X0)
% 0.61/0.80          | ~ (v2_pre_topc @ X0)
% 0.61/0.80          | ~ (l1_pre_topc @ X0)
% 0.61/0.80          | (v2_tex_2 @ X1 @ X0)
% 0.61/0.80          | ~ (v1_xboole_0 @ X1))),
% 0.61/0.80      inference('sup-', [status(thm)], ['15', '16'])).
% 0.61/0.80  thf('18', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((v2_tex_2 @ X1 @ X0)
% 0.61/0.80          | ~ (l1_pre_topc @ X0)
% 0.61/0.80          | ~ (v2_pre_topc @ X0)
% 0.61/0.80          | (v2_struct_0 @ X0)
% 0.61/0.80          | ~ (v1_xboole_0 @ X1))),
% 0.61/0.80      inference('simplify', [status(thm)], ['17'])).
% 0.61/0.80  thf('19', plain,
% 0.61/0.80      (![X0 : $i]:
% 0.61/0.80         (~ (v1_xboole_0 @ X0)
% 0.61/0.80          | (v2_struct_0 @ sk_A)
% 0.61/0.80          | ~ (v2_pre_topc @ sk_A)
% 0.61/0.80          | (v2_tex_2 @ X0 @ sk_A))),
% 0.61/0.80      inference('sup-', [status(thm)], ['0', '18'])).
% 0.61/0.80  thf('20', plain, ((v2_pre_topc @ sk_A)),
% 0.61/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.80  thf('21', plain,
% 0.61/0.80      (![X0 : $i]:
% 0.61/0.80         (~ (v1_xboole_0 @ X0) | (v2_struct_0 @ sk_A) | (v2_tex_2 @ X0 @ sk_A))),
% 0.61/0.80      inference('demod', [status(thm)], ['19', '20'])).
% 0.61/0.80  thf('22', plain, (~ (v2_struct_0 @ sk_A)),
% 0.61/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.80  thf('23', plain,
% 0.61/0.80      (![X0 : $i]: ((v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.61/0.80      inference('clc', [status(thm)], ['21', '22'])).
% 0.61/0.80  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.61/0.80  thf('24', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.61/0.80      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.61/0.80  thf('25', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.61/0.80      inference('sup-', [status(thm)], ['5', '8'])).
% 0.61/0.80  thf('26', plain,
% 0.61/0.80      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.61/0.80      inference('sup-', [status(thm)], ['24', '25'])).
% 0.61/0.80  thf('27', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.61/0.80      inference('sup-', [status(thm)], ['12', '13'])).
% 0.61/0.80  thf('28', plain,
% 0.61/0.80      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.61/0.80      inference('sup+', [status(thm)], ['26', '27'])).
% 0.61/0.80  thf(t65_tex_2, axiom,
% 0.61/0.80    (![A:$i]:
% 0.61/0.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.61/0.80         ( l1_pre_topc @ A ) ) =>
% 0.61/0.80       ( ![B:$i]:
% 0.61/0.80         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.61/0.80           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.61/0.80                ( ![C:$i]:
% 0.61/0.80                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.61/0.80                    ( ~( ( r1_tarski @ B @ C ) & ( v3_tex_2 @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.61/0.80  thf('29', plain,
% 0.61/0.80      (![X13 : $i, X14 : $i]:
% 0.61/0.80         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.61/0.80          | ~ (v2_tex_2 @ X13 @ X14)
% 0.61/0.80          | (m1_subset_1 @ (sk_C @ X13 @ X14) @ 
% 0.61/0.80             (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.61/0.80          | ~ (l1_pre_topc @ X14)
% 0.61/0.80          | ~ (v3_tdlat_3 @ X14)
% 0.61/0.80          | ~ (v2_pre_topc @ X14)
% 0.61/0.80          | (v2_struct_0 @ X14))),
% 0.61/0.80      inference('cnf', [status(esa)], [t65_tex_2])).
% 0.61/0.80  thf('30', plain,
% 0.61/0.80      (![X0 : $i]:
% 0.61/0.80         ((v2_struct_0 @ X0)
% 0.61/0.80          | ~ (v2_pre_topc @ X0)
% 0.61/0.80          | ~ (v3_tdlat_3 @ X0)
% 0.61/0.80          | ~ (l1_pre_topc @ X0)
% 0.61/0.80          | (m1_subset_1 @ (sk_C @ k1_xboole_0 @ X0) @ 
% 0.61/0.80             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.61/0.80          | ~ (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.61/0.80      inference('sup-', [status(thm)], ['28', '29'])).
% 0.61/0.80  thf('31', plain,
% 0.61/0.80      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.61/0.80        | (m1_subset_1 @ (sk_C @ k1_xboole_0 @ sk_A) @ 
% 0.61/0.80           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.80        | ~ (l1_pre_topc @ sk_A)
% 0.61/0.80        | ~ (v3_tdlat_3 @ sk_A)
% 0.61/0.80        | ~ (v2_pre_topc @ sk_A)
% 0.61/0.80        | (v2_struct_0 @ sk_A))),
% 0.61/0.80      inference('sup-', [status(thm)], ['23', '30'])).
% 0.61/0.80  thf('32', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.61/0.80      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.61/0.80  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.80  thf('34', plain, ((v3_tdlat_3 @ sk_A)),
% 0.61/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.80  thf('35', plain, ((v2_pre_topc @ sk_A)),
% 0.61/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.80  thf('36', plain,
% 0.61/0.80      (((m1_subset_1 @ (sk_C @ k1_xboole_0 @ sk_A) @ 
% 0.61/0.80         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.80        | (v2_struct_0 @ sk_A))),
% 0.61/0.80      inference('demod', [status(thm)], ['31', '32', '33', '34', '35'])).
% 0.61/0.80  thf('37', plain, (~ (v2_struct_0 @ sk_A)),
% 0.61/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.80  thf('38', plain,
% 0.61/0.80      ((m1_subset_1 @ (sk_C @ k1_xboole_0 @ sk_A) @ 
% 0.61/0.80        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.61/0.80      inference('clc', [status(thm)], ['36', '37'])).
% 0.61/0.80  thf('39', plain,
% 0.61/0.80      (![X15 : $i]:
% 0.61/0.80         (~ (v3_tex_2 @ X15 @ sk_A)
% 0.61/0.80          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.61/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.80  thf('40', plain, (~ (v3_tex_2 @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_A)),
% 0.61/0.80      inference('sup-', [status(thm)], ['38', '39'])).
% 0.61/0.80  thf('41', plain,
% 0.61/0.80      (![X0 : $i]: ((v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.61/0.80      inference('clc', [status(thm)], ['21', '22'])).
% 0.61/0.80  thf('42', plain,
% 0.61/0.80      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.61/0.80      inference('sup-', [status(thm)], ['24', '25'])).
% 0.61/0.80  thf('43', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.61/0.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.61/0.80  thf('44', plain,
% 0.61/0.80      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.61/0.80      inference('sup+', [status(thm)], ['42', '43'])).
% 0.61/0.80  thf('45', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.61/0.80      inference('sup-', [status(thm)], ['1', '2'])).
% 0.61/0.80  thf('46', plain,
% 0.61/0.80      (![X13 : $i, X14 : $i]:
% 0.61/0.80         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.61/0.80          | ~ (v2_tex_2 @ X13 @ X14)
% 0.61/0.80          | (v3_tex_2 @ (sk_C @ X13 @ X14) @ X14)
% 0.61/0.80          | ~ (l1_pre_topc @ X14)
% 0.61/0.80          | ~ (v3_tdlat_3 @ X14)
% 0.61/0.80          | ~ (v2_pre_topc @ X14)
% 0.61/0.80          | (v2_struct_0 @ X14))),
% 0.61/0.80      inference('cnf', [status(esa)], [t65_tex_2])).
% 0.61/0.80  thf('47', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((v2_struct_0 @ X0)
% 0.61/0.80          | ~ (v2_pre_topc @ X0)
% 0.61/0.80          | ~ (v3_tdlat_3 @ X0)
% 0.61/0.80          | ~ (l1_pre_topc @ X0)
% 0.61/0.80          | (v3_tex_2 @ 
% 0.61/0.80             (sk_C @ (k3_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0) @ X0)
% 0.61/0.80          | ~ (v2_tex_2 @ (k3_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0))),
% 0.61/0.80      inference('sup-', [status(thm)], ['45', '46'])).
% 0.61/0.80  thf('48', plain,
% 0.61/0.80      (![X0 : $i]:
% 0.61/0.80         (~ (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.61/0.80          | (v3_tex_2 @ 
% 0.61/0.80             (sk_C @ (k3_xboole_0 @ (u1_struct_0 @ X0) @ k1_xboole_0) @ X0) @ 
% 0.61/0.80             X0)
% 0.61/0.80          | ~ (l1_pre_topc @ X0)
% 0.61/0.80          | ~ (v3_tdlat_3 @ X0)
% 0.61/0.80          | ~ (v2_pre_topc @ X0)
% 0.61/0.80          | (v2_struct_0 @ X0))),
% 0.61/0.80      inference('sup-', [status(thm)], ['44', '47'])).
% 0.61/0.80  thf('49', plain,
% 0.61/0.80      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.61/0.80      inference('sup+', [status(thm)], ['42', '43'])).
% 0.61/0.80  thf('50', plain,
% 0.61/0.80      (![X0 : $i]:
% 0.61/0.80         (~ (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.61/0.80          | (v3_tex_2 @ (sk_C @ k1_xboole_0 @ X0) @ X0)
% 0.61/0.80          | ~ (l1_pre_topc @ X0)
% 0.61/0.80          | ~ (v3_tdlat_3 @ X0)
% 0.61/0.80          | ~ (v2_pre_topc @ X0)
% 0.61/0.80          | (v2_struct_0 @ X0))),
% 0.61/0.80      inference('demod', [status(thm)], ['48', '49'])).
% 0.61/0.80  thf('51', plain,
% 0.61/0.80      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.61/0.80        | (v2_struct_0 @ sk_A)
% 0.61/0.80        | ~ (v2_pre_topc @ sk_A)
% 0.61/0.80        | ~ (v3_tdlat_3 @ sk_A)
% 0.61/0.80        | ~ (l1_pre_topc @ sk_A)
% 0.61/0.80        | (v3_tex_2 @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_A))),
% 0.61/0.80      inference('sup-', [status(thm)], ['41', '50'])).
% 0.61/0.80  thf('52', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.61/0.80      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.61/0.80  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.61/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.80  thf('54', plain, ((v3_tdlat_3 @ sk_A)),
% 0.61/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.80  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.80  thf('56', plain,
% 0.61/0.80      (((v2_struct_0 @ sk_A) | (v3_tex_2 @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_A))),
% 0.61/0.80      inference('demod', [status(thm)], ['51', '52', '53', '54', '55'])).
% 0.61/0.80  thf('57', plain, (~ (v2_struct_0 @ sk_A)),
% 0.61/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.80  thf('58', plain, ((v3_tex_2 @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_A)),
% 0.61/0.80      inference('clc', [status(thm)], ['56', '57'])).
% 0.61/0.80  thf('59', plain, ($false), inference('demod', [status(thm)], ['40', '58'])).
% 0.61/0.80  
% 0.61/0.80  % SZS output end Refutation
% 0.61/0.80  
% 0.66/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
