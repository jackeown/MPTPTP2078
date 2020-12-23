%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HHCf7njBZz

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:26 EST 2020

% Result     : Theorem 7.10s
% Output     : Refutation 7.10s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 146 expanded)
%              Number of leaves         :   30 (  57 expanded)
%              Depth                    :   15
%              Number of atoms          :  641 (1051 expanded)
%              Number of equality atoms :   44 (  62 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

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

thf('3',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( r1_tarski @ ( sk_C @ X37 @ X38 ) @ X37 )
      | ( v2_tex_2 @ X37 @ X38 )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ X1 @ X0 )
      | ( r1_tarski @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('11',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

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

thf('14',plain,(
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('17',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,
    ( ( ( sk_C @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('23',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('26',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( v4_pre_topc @ X35 @ X36 )
      | ~ ( v1_xboole_0 @ X35 )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v4_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','28'])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('33',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('34',plain,(
    ! [X37: $i,X38: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( v4_pre_topc @ X40 @ X38 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X38 ) @ X37 @ X40 )
       != ( sk_C @ X37 @ X38 ) )
      | ( v2_tex_2 @ X37 @ X38 )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ X1 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v4_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('37',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k9_subset_1 @ X18 @ X16 @ X17 )
        = ( k3_xboole_0 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('40',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['39'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('41',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('43',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('44',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['39'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('48',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('55',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k9_subset_1 @ X13 @ X15 @ X14 )
        = ( k9_subset_1 @ X13 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k9_subset_1 @ X0 @ X2 @ X1 )
        = ( k9_subset_1 @ X0 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k9_subset_1 @ X1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['53','56'])).

thf('58',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k9_subset_1 @ X1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v4_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['35','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','60'])).

thf('62',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0
     != ( sk_C @ k1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','61'])).

thf('63',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0
     != ( sk_C @ k1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('67',plain,(
    k1_xboole_0
 != ( sk_C @ k1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['23','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HHCf7njBZz
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:11:09 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 7.10/7.28  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 7.10/7.28  % Solved by: fo/fo7.sh
% 7.10/7.28  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.10/7.28  % done 15552 iterations in 6.800s
% 7.10/7.28  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 7.10/7.28  % SZS output start Refutation
% 7.10/7.28  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 7.10/7.28  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 7.10/7.28  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 7.10/7.28  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 7.10/7.28  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 7.10/7.28  thf(sk_B_1_type, type, sk_B_1: $i).
% 7.10/7.28  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 7.10/7.28  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 7.10/7.28  thf(sk_A_type, type, sk_A: $i).
% 7.10/7.28  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 7.10/7.28  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 7.10/7.28  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 7.10/7.28  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 7.10/7.28  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 7.10/7.28  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 7.10/7.28  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 7.10/7.28  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.10/7.28  thf(l13_xboole_0, axiom,
% 7.10/7.28    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 7.10/7.28  thf('0', plain,
% 7.10/7.28      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 7.10/7.28      inference('cnf', [status(esa)], [l13_xboole_0])).
% 7.10/7.28  thf(t4_subset_1, axiom,
% 7.10/7.28    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 7.10/7.28  thf('1', plain,
% 7.10/7.28      (![X19 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X19))),
% 7.10/7.28      inference('cnf', [status(esa)], [t4_subset_1])).
% 7.10/7.28  thf('2', plain,
% 7.10/7.28      (![X0 : $i, X1 : $i]:
% 7.10/7.28         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 7.10/7.28      inference('sup+', [status(thm)], ['0', '1'])).
% 7.10/7.28  thf(d6_tex_2, axiom,
% 7.10/7.28    (![A:$i]:
% 7.10/7.28     ( ( l1_pre_topc @ A ) =>
% 7.10/7.28       ( ![B:$i]:
% 7.10/7.28         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.10/7.28           ( ( v2_tex_2 @ B @ A ) <=>
% 7.10/7.28             ( ![C:$i]:
% 7.10/7.28               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.10/7.28                 ( ~( ( r1_tarski @ C @ B ) & 
% 7.10/7.28                      ( ![D:$i]:
% 7.10/7.28                        ( ( m1_subset_1 @
% 7.10/7.28                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.10/7.28                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 7.10/7.28                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 7.10/7.28                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 7.10/7.28  thf('3', plain,
% 7.10/7.28      (![X37 : $i, X38 : $i]:
% 7.10/7.28         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 7.10/7.28          | (r1_tarski @ (sk_C @ X37 @ X38) @ X37)
% 7.10/7.28          | (v2_tex_2 @ X37 @ X38)
% 7.10/7.28          | ~ (l1_pre_topc @ X38))),
% 7.10/7.28      inference('cnf', [status(esa)], [d6_tex_2])).
% 7.10/7.28  thf('4', plain,
% 7.10/7.28      (![X0 : $i, X1 : $i]:
% 7.10/7.28         (~ (v1_xboole_0 @ X1)
% 7.10/7.28          | ~ (l1_pre_topc @ X0)
% 7.10/7.28          | (v2_tex_2 @ X1 @ X0)
% 7.10/7.28          | (r1_tarski @ (sk_C @ X1 @ X0) @ X1))),
% 7.10/7.28      inference('sup-', [status(thm)], ['2', '3'])).
% 7.10/7.28  thf('5', plain,
% 7.10/7.28      (![X19 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X19))),
% 7.10/7.28      inference('cnf', [status(esa)], [t4_subset_1])).
% 7.10/7.28  thf(t3_subset, axiom,
% 7.10/7.28    (![A:$i,B:$i]:
% 7.10/7.28     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 7.10/7.28  thf('6', plain,
% 7.10/7.28      (![X22 : $i, X23 : $i]:
% 7.10/7.28         ((r1_tarski @ X22 @ X23) | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 7.10/7.28      inference('cnf', [status(esa)], [t3_subset])).
% 7.10/7.28  thf('7', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 7.10/7.28      inference('sup-', [status(thm)], ['5', '6'])).
% 7.10/7.28  thf(d10_xboole_0, axiom,
% 7.10/7.28    (![A:$i,B:$i]:
% 7.10/7.28     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 7.10/7.28  thf('8', plain,
% 7.10/7.28      (![X1 : $i, X3 : $i]:
% 7.10/7.28         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 7.10/7.28      inference('cnf', [status(esa)], [d10_xboole_0])).
% 7.10/7.28  thf('9', plain,
% 7.10/7.28      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 7.10/7.28      inference('sup-', [status(thm)], ['7', '8'])).
% 7.10/7.28  thf('10', plain,
% 7.10/7.28      (![X0 : $i]:
% 7.10/7.28         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 7.10/7.28          | ~ (l1_pre_topc @ X0)
% 7.10/7.28          | ~ (v1_xboole_0 @ k1_xboole_0)
% 7.10/7.28          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 7.10/7.28      inference('sup-', [status(thm)], ['4', '9'])).
% 7.10/7.28  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 7.10/7.28  thf('11', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 7.10/7.28      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 7.10/7.28  thf('12', plain,
% 7.10/7.28      (![X0 : $i]:
% 7.10/7.28         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 7.10/7.28          | ~ (l1_pre_topc @ X0)
% 7.10/7.28          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 7.10/7.28      inference('demod', [status(thm)], ['10', '11'])).
% 7.10/7.28  thf('13', plain,
% 7.10/7.28      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 7.10/7.28      inference('cnf', [status(esa)], [l13_xboole_0])).
% 7.10/7.28  thf(t35_tex_2, conjecture,
% 7.10/7.28    (![A:$i]:
% 7.10/7.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 7.10/7.28       ( ![B:$i]:
% 7.10/7.28         ( ( ( v1_xboole_0 @ B ) & 
% 7.10/7.28             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 7.10/7.28           ( v2_tex_2 @ B @ A ) ) ) ))).
% 7.10/7.28  thf(zf_stmt_0, negated_conjecture,
% 7.10/7.28    (~( ![A:$i]:
% 7.10/7.28        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 7.10/7.28            ( l1_pre_topc @ A ) ) =>
% 7.10/7.28          ( ![B:$i]:
% 7.10/7.28            ( ( ( v1_xboole_0 @ B ) & 
% 7.10/7.28                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 7.10/7.28              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 7.10/7.28    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 7.10/7.28  thf('14', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 7.10/7.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.10/7.28  thf('15', plain, ((v1_xboole_0 @ sk_B_1)),
% 7.10/7.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.10/7.28  thf('16', plain,
% 7.10/7.28      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 7.10/7.28      inference('cnf', [status(esa)], [l13_xboole_0])).
% 7.10/7.28  thf('17', plain, (((sk_B_1) = (k1_xboole_0))),
% 7.10/7.28      inference('sup-', [status(thm)], ['15', '16'])).
% 7.10/7.28  thf('18', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 7.10/7.28      inference('demod', [status(thm)], ['14', '17'])).
% 7.10/7.28  thf('19', plain,
% 7.10/7.28      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 7.10/7.28      inference('sup-', [status(thm)], ['13', '18'])).
% 7.10/7.28  thf('20', plain,
% 7.10/7.28      ((((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))
% 7.10/7.28        | ~ (l1_pre_topc @ sk_A)
% 7.10/7.28        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 7.10/7.28      inference('sup-', [status(thm)], ['12', '19'])).
% 7.10/7.28  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 7.10/7.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.10/7.28  thf('22', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 7.10/7.28      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 7.10/7.28  thf('23', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 7.10/7.28      inference('demod', [status(thm)], ['20', '21', '22'])).
% 7.10/7.28  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 7.10/7.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.10/7.28  thf('25', plain,
% 7.10/7.28      (![X0 : $i, X1 : $i]:
% 7.10/7.28         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 7.10/7.28      inference('sup+', [status(thm)], ['0', '1'])).
% 7.10/7.28  thf(cc2_pre_topc, axiom,
% 7.10/7.28    (![A:$i]:
% 7.10/7.28     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 7.10/7.28       ( ![B:$i]:
% 7.10/7.28         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.10/7.28           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 7.10/7.28  thf('26', plain,
% 7.10/7.28      (![X35 : $i, X36 : $i]:
% 7.10/7.28         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 7.10/7.28          | (v4_pre_topc @ X35 @ X36)
% 7.10/7.28          | ~ (v1_xboole_0 @ X35)
% 7.10/7.28          | ~ (l1_pre_topc @ X36)
% 7.10/7.28          | ~ (v2_pre_topc @ X36))),
% 7.10/7.28      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 7.10/7.28  thf('27', plain,
% 7.10/7.28      (![X0 : $i, X1 : $i]:
% 7.10/7.28         (~ (v1_xboole_0 @ X1)
% 7.10/7.28          | ~ (v2_pre_topc @ X0)
% 7.10/7.28          | ~ (l1_pre_topc @ X0)
% 7.10/7.28          | ~ (v1_xboole_0 @ X1)
% 7.10/7.28          | (v4_pre_topc @ X1 @ X0))),
% 7.10/7.28      inference('sup-', [status(thm)], ['25', '26'])).
% 7.10/7.28  thf('28', plain,
% 7.10/7.28      (![X0 : $i, X1 : $i]:
% 7.10/7.28         ((v4_pre_topc @ X1 @ X0)
% 7.10/7.28          | ~ (l1_pre_topc @ X0)
% 7.10/7.28          | ~ (v2_pre_topc @ X0)
% 7.10/7.28          | ~ (v1_xboole_0 @ X1))),
% 7.10/7.28      inference('simplify', [status(thm)], ['27'])).
% 7.10/7.28  thf('29', plain,
% 7.10/7.28      (![X0 : $i]:
% 7.10/7.28         (~ (v1_xboole_0 @ X0)
% 7.10/7.28          | ~ (v2_pre_topc @ sk_A)
% 7.10/7.28          | (v4_pre_topc @ X0 @ sk_A))),
% 7.10/7.28      inference('sup-', [status(thm)], ['24', '28'])).
% 7.10/7.28  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 7.10/7.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.10/7.28  thf('31', plain,
% 7.10/7.28      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v4_pre_topc @ X0 @ sk_A))),
% 7.10/7.28      inference('demod', [status(thm)], ['29', '30'])).
% 7.10/7.28  thf('32', plain,
% 7.10/7.28      (![X19 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X19))),
% 7.10/7.28      inference('cnf', [status(esa)], [t4_subset_1])).
% 7.10/7.28  thf('33', plain,
% 7.10/7.28      (![X19 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X19))),
% 7.10/7.28      inference('cnf', [status(esa)], [t4_subset_1])).
% 7.10/7.28  thf('34', plain,
% 7.10/7.28      (![X37 : $i, X38 : $i, X40 : $i]:
% 7.10/7.28         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 7.10/7.28          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 7.10/7.28          | ~ (v4_pre_topc @ X40 @ X38)
% 7.10/7.28          | ((k9_subset_1 @ (u1_struct_0 @ X38) @ X37 @ X40)
% 7.10/7.28              != (sk_C @ X37 @ X38))
% 7.10/7.28          | (v2_tex_2 @ X37 @ X38)
% 7.10/7.28          | ~ (l1_pre_topc @ X38))),
% 7.10/7.28      inference('cnf', [status(esa)], [d6_tex_2])).
% 7.10/7.28  thf('35', plain,
% 7.10/7.28      (![X0 : $i, X1 : $i]:
% 7.10/7.28         (~ (l1_pre_topc @ X0)
% 7.10/7.28          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 7.10/7.28          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 7.10/7.28              != (sk_C @ k1_xboole_0 @ X0))
% 7.10/7.28          | ~ (v4_pre_topc @ X1 @ X0)
% 7.10/7.28          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 7.10/7.28      inference('sup-', [status(thm)], ['33', '34'])).
% 7.10/7.28  thf('36', plain,
% 7.10/7.28      (![X19 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X19))),
% 7.10/7.28      inference('cnf', [status(esa)], [t4_subset_1])).
% 7.10/7.28  thf(redefinition_k9_subset_1, axiom,
% 7.10/7.28    (![A:$i,B:$i,C:$i]:
% 7.10/7.28     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 7.10/7.28       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 7.10/7.28  thf('37', plain,
% 7.10/7.28      (![X16 : $i, X17 : $i, X18 : $i]:
% 7.10/7.28         (((k9_subset_1 @ X18 @ X16 @ X17) = (k3_xboole_0 @ X16 @ X17))
% 7.10/7.28          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 7.10/7.28      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 7.10/7.28  thf('38', plain,
% 7.10/7.28      (![X0 : $i, X1 : $i]:
% 7.10/7.28         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 7.10/7.28           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 7.10/7.28      inference('sup-', [status(thm)], ['36', '37'])).
% 7.10/7.28  thf('39', plain,
% 7.10/7.28      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 7.10/7.28      inference('cnf', [status(esa)], [d10_xboole_0])).
% 7.10/7.28  thf('40', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 7.10/7.28      inference('simplify', [status(thm)], ['39'])).
% 7.10/7.28  thf(l32_xboole_1, axiom,
% 7.10/7.28    (![A:$i,B:$i]:
% 7.10/7.28     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 7.10/7.28  thf('41', plain,
% 7.10/7.28      (![X4 : $i, X6 : $i]:
% 7.10/7.28         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 7.10/7.28      inference('cnf', [status(esa)], [l32_xboole_1])).
% 7.10/7.28  thf('42', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 7.10/7.28      inference('sup-', [status(thm)], ['40', '41'])).
% 7.10/7.28  thf(t48_xboole_1, axiom,
% 7.10/7.28    (![A:$i,B:$i]:
% 7.10/7.28     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 7.10/7.28  thf('43', plain,
% 7.10/7.28      (![X11 : $i, X12 : $i]:
% 7.10/7.28         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 7.10/7.28           = (k3_xboole_0 @ X11 @ X12))),
% 7.10/7.28      inference('cnf', [status(esa)], [t48_xboole_1])).
% 7.10/7.28  thf('44', plain,
% 7.10/7.28      (![X11 : $i, X12 : $i]:
% 7.10/7.28         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 7.10/7.28           = (k3_xboole_0 @ X11 @ X12))),
% 7.10/7.28      inference('cnf', [status(esa)], [t48_xboole_1])).
% 7.10/7.28  thf('45', plain,
% 7.10/7.28      (![X0 : $i, X1 : $i]:
% 7.10/7.28         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 7.10/7.28           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 7.10/7.28      inference('sup+', [status(thm)], ['43', '44'])).
% 7.10/7.28  thf('46', plain,
% 7.10/7.28      (![X0 : $i]:
% 7.10/7.28         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0))
% 7.10/7.28           = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 7.10/7.28      inference('sup+', [status(thm)], ['42', '45'])).
% 7.10/7.28  thf('47', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 7.10/7.28      inference('simplify', [status(thm)], ['39'])).
% 7.10/7.28  thf(t28_xboole_1, axiom,
% 7.10/7.28    (![A:$i,B:$i]:
% 7.10/7.28     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 7.10/7.28  thf('48', plain,
% 7.10/7.28      (![X7 : $i, X8 : $i]:
% 7.10/7.28         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 7.10/7.28      inference('cnf', [status(esa)], [t28_xboole_1])).
% 7.10/7.28  thf('49', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 7.10/7.28      inference('sup-', [status(thm)], ['47', '48'])).
% 7.10/7.28  thf('50', plain,
% 7.10/7.28      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 7.10/7.28      inference('demod', [status(thm)], ['46', '49'])).
% 7.10/7.28  thf('51', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 7.10/7.28      inference('sup-', [status(thm)], ['40', '41'])).
% 7.10/7.28  thf('52', plain,
% 7.10/7.28      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 7.10/7.28      inference('sup+', [status(thm)], ['50', '51'])).
% 7.10/7.28  thf('53', plain,
% 7.10/7.28      (![X0 : $i, X1 : $i]:
% 7.10/7.28         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 7.10/7.28      inference('demod', [status(thm)], ['38', '52'])).
% 7.10/7.28  thf('54', plain,
% 7.10/7.28      (![X0 : $i, X1 : $i]:
% 7.10/7.28         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 7.10/7.28      inference('sup+', [status(thm)], ['0', '1'])).
% 7.10/7.28  thf(commutativity_k9_subset_1, axiom,
% 7.10/7.28    (![A:$i,B:$i,C:$i]:
% 7.10/7.28     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 7.10/7.28       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 7.10/7.28  thf('55', plain,
% 7.10/7.28      (![X13 : $i, X14 : $i, X15 : $i]:
% 7.10/7.28         (((k9_subset_1 @ X13 @ X15 @ X14) = (k9_subset_1 @ X13 @ X14 @ X15))
% 7.10/7.28          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 7.10/7.28      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 7.10/7.28  thf('56', plain,
% 7.10/7.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.10/7.28         (~ (v1_xboole_0 @ X1)
% 7.10/7.28          | ((k9_subset_1 @ X0 @ X2 @ X1) = (k9_subset_1 @ X0 @ X1 @ X2)))),
% 7.10/7.28      inference('sup-', [status(thm)], ['54', '55'])).
% 7.10/7.28  thf('57', plain,
% 7.10/7.28      (![X0 : $i, X1 : $i]:
% 7.10/7.28         (((k1_xboole_0) = (k9_subset_1 @ X1 @ k1_xboole_0 @ X0))
% 7.10/7.28          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 7.10/7.28      inference('sup+', [status(thm)], ['53', '56'])).
% 7.10/7.28  thf('58', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 7.10/7.28      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 7.10/7.28  thf('59', plain,
% 7.10/7.28      (![X0 : $i, X1 : $i]:
% 7.10/7.28         ((k1_xboole_0) = (k9_subset_1 @ X1 @ k1_xboole_0 @ X0))),
% 7.10/7.28      inference('demod', [status(thm)], ['57', '58'])).
% 7.10/7.28  thf('60', plain,
% 7.10/7.28      (![X0 : $i, X1 : $i]:
% 7.10/7.28         (~ (l1_pre_topc @ X0)
% 7.10/7.28          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 7.10/7.28          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 7.10/7.28          | ~ (v4_pre_topc @ X1 @ X0)
% 7.10/7.28          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 7.10/7.28      inference('demod', [status(thm)], ['35', '59'])).
% 7.10/7.28  thf('61', plain,
% 7.10/7.28      (![X0 : $i]:
% 7.10/7.28         (~ (v4_pre_topc @ k1_xboole_0 @ X0)
% 7.10/7.28          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 7.10/7.28          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 7.10/7.28          | ~ (l1_pre_topc @ X0))),
% 7.10/7.28      inference('sup-', [status(thm)], ['32', '60'])).
% 7.10/7.28  thf('62', plain,
% 7.10/7.28      ((~ (v1_xboole_0 @ k1_xboole_0)
% 7.10/7.28        | ~ (l1_pre_topc @ sk_A)
% 7.10/7.28        | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 7.10/7.28        | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ sk_A)))),
% 7.10/7.28      inference('sup-', [status(thm)], ['31', '61'])).
% 7.10/7.28  thf('63', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 7.10/7.28      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 7.10/7.28  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 7.10/7.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.10/7.28  thf('65', plain,
% 7.10/7.28      (((v2_tex_2 @ k1_xboole_0 @ sk_A)
% 7.10/7.28        | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ sk_A)))),
% 7.10/7.28      inference('demod', [status(thm)], ['62', '63', '64'])).
% 7.10/7.28  thf('66', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 7.10/7.28      inference('demod', [status(thm)], ['14', '17'])).
% 7.10/7.28  thf('67', plain, (((k1_xboole_0) != (sk_C @ k1_xboole_0 @ sk_A))),
% 7.10/7.28      inference('clc', [status(thm)], ['65', '66'])).
% 7.10/7.28  thf('68', plain, ($false),
% 7.10/7.28      inference('simplify_reflect-', [status(thm)], ['23', '67'])).
% 7.10/7.28  
% 7.10/7.28  % SZS output end Refutation
% 7.10/7.28  
% 7.10/7.29  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
