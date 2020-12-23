%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jCQoPlKJXW

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:32 EST 2020

% Result     : Theorem 6.18s
% Output     : Refutation 6.18s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 492 expanded)
%              Number of leaves         :   29 ( 164 expanded)
%              Depth                    :   28
%              Number of atoms          : 1347 (3755 expanded)
%              Number of equality atoms :   97 ( 263 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

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
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v4_pre_topc @ X19 @ X20 )
      | ~ ( v1_xboole_0 @ X19 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v4_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
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

thf('7',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( r1_tarski @ ( sk_C @ X21 @ X22 ) @ X21 )
      | ( v2_tex_2 @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ X1 @ X0 )
      | ( r1_tarski @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('10',plain,(
    ! [X9: $i] :
      ( r1_tarski @ k1_xboole_0 @ X9 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_tex_2 @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( sk_C @ X0 @ X1 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_tex_2 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
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

thf('17',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_xboole_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('20',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( sk_C @ X0 @ sk_A )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( sk_C @ X0 @ sk_A )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ sk_A )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['27'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('29',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ X1 @ X0 )
      | ( r1_tarski @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('33',plain,(
    ! [X9: $i] :
      ( r1_tarski @ k1_xboole_0 @ X9 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('34',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('37',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('40',plain,
    ( ( ( sk_C @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('43',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('46',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( m1_subset_1 @ ( sk_C @ X21 @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v2_tex_2 @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ X1 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('48',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k9_subset_1 @ X14 @ X12 @ X13 )
        = ( k3_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_tex_2 @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X2 @ ( sk_C @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X2 @ ( sk_C @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 @ k1_xboole_0 )
        = ( k3_xboole_0 @ X1 @ ( sk_C @ X0 @ sk_A ) ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_tex_2 @ X0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['44','49'])).

thf('51',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('52',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k9_subset_1 @ X14 @ X12 @ X13 )
        = ( k3_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

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
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['27'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('58',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('64',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X1 @ ( sk_C @ X0 @ sk_A ) ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v2_tex_2 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X1 @ ( sk_C @ X0 @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X1 @ ( sk_C @ X0 @ sk_A ) ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('76',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( ( k4_xboole_0 @ X4 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('83',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['81','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['71','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ ( k4_xboole_0 @ X1 @ ( sk_C @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['70','86'])).

thf('88',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ ( k4_xboole_0 @ X1 @ ( sk_C @ X0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( sk_C @ X0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','89'])).

thf('91',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( sk_C @ X0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('94',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k3_xboole_0 @ ( sk_C @ X0 @ sk_A ) @ X1 )
        = ( sk_C @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = ( sk_C @ X0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = ( sk_C @ X0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('102',plain,(
    ! [X9: $i] :
      ( r1_tarski @ k1_xboole_0 @ X9 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('103',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['101','104'])).

thf('106',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X2 )
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['100','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['101','104'])).

thf('114',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k9_subset_1 @ X14 @ X12 @ X13 )
        = ( k3_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( ( k9_subset_1 @ X0 @ X3 @ ( k3_xboole_0 @ X2 @ X1 ) )
        = ( k3_xboole_0 @ X3 @ ( k3_xboole_0 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k9_subset_1 @ X3 @ X2 @ X0 )
        = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['112','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ X3 @ X2 @ X0 )
        = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_subset_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k9_subset_1 @ X3 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['111','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k9_subset_1 @ X3 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
        = ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_subset_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['99','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k9_subset_1 @ X2 @ ( sk_C @ X0 @ sk_A ) @ X0 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['98','125'])).

thf('127',plain,(
    ! [X0: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ X2 @ ( sk_C @ X0 @ sk_A ) @ X0 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('129',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( m1_subset_1 @ ( sk_C @ X21 @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v2_tex_2 @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X21: $i,X22: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v4_pre_topc @ X24 @ X22 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X22 ) @ X21 @ X24 )
       != ( sk_C @ X21 @ X22 ) )
      | ( v2_tex_2 @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( sk_C @ k1_xboole_0 @ X0 ) @ X1 )
       != ( sk_C @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 ) )
      | ~ ( v4_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v4_pre_topc @ X1 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( sk_C @ k1_xboole_0 @ X0 ) @ X1 )
       != ( sk_C @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 ) )
      | ( v2_tex_2 @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,
    ( ( k1_xboole_0
     != ( sk_C @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_A ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_A )
    | ~ ( v4_pre_topc @ k1_xboole_0 @ sk_A )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['127','133'])).

thf('135',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('136',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('137',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('138',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('140',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('141',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ~ ( v4_pre_topc @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['134','135','136','137','138','139','140'])).

thf('142',plain,
    ( ~ ( v4_pre_topc @ k1_xboole_0 @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('144',plain,(
    ~ ( v4_pre_topc @ k1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['142','143'])).

thf('145',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['5','144'])).

thf('146',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('147',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    $false ),
    inference(demod,[status(thm)],['145','146','147','148'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jCQoPlKJXW
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:19:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 6.18/6.40  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.18/6.40  % Solved by: fo/fo7.sh
% 6.18/6.40  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.18/6.40  % done 12476 iterations in 5.929s
% 6.18/6.40  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.18/6.40  % SZS output start Refutation
% 6.18/6.40  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 6.18/6.40  thf(sk_B_type, type, sk_B: $i).
% 6.18/6.40  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 6.18/6.40  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 6.18/6.40  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 6.18/6.40  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.18/6.40  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 6.18/6.40  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.18/6.40  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 6.18/6.40  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 6.18/6.40  thf(sk_A_type, type, sk_A: $i).
% 6.18/6.40  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 6.18/6.40  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 6.18/6.40  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.18/6.40  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 6.18/6.40  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 6.18/6.40  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.18/6.40  thf(l13_xboole_0, axiom,
% 6.18/6.40    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 6.18/6.40  thf('0', plain,
% 6.18/6.40      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.18/6.40      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.18/6.40  thf(t4_subset_1, axiom,
% 6.18/6.40    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 6.18/6.40  thf('1', plain,
% 6.18/6.40      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 6.18/6.40      inference('cnf', [status(esa)], [t4_subset_1])).
% 6.18/6.40  thf('2', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i]:
% 6.18/6.40         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 6.18/6.40      inference('sup+', [status(thm)], ['0', '1'])).
% 6.18/6.40  thf(cc2_pre_topc, axiom,
% 6.18/6.40    (![A:$i]:
% 6.18/6.40     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.18/6.40       ( ![B:$i]:
% 6.18/6.40         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.18/6.40           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 6.18/6.40  thf('3', plain,
% 6.18/6.40      (![X19 : $i, X20 : $i]:
% 6.18/6.40         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 6.18/6.40          | (v4_pre_topc @ X19 @ X20)
% 6.18/6.40          | ~ (v1_xboole_0 @ X19)
% 6.18/6.40          | ~ (l1_pre_topc @ X20)
% 6.18/6.40          | ~ (v2_pre_topc @ X20))),
% 6.18/6.40      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 6.18/6.40  thf('4', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i]:
% 6.18/6.40         (~ (v1_xboole_0 @ X1)
% 6.18/6.40          | ~ (v2_pre_topc @ X0)
% 6.18/6.40          | ~ (l1_pre_topc @ X0)
% 6.18/6.40          | ~ (v1_xboole_0 @ X1)
% 6.18/6.40          | (v4_pre_topc @ X1 @ X0))),
% 6.18/6.40      inference('sup-', [status(thm)], ['2', '3'])).
% 6.18/6.40  thf('5', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i]:
% 6.18/6.40         ((v4_pre_topc @ X1 @ X0)
% 6.18/6.40          | ~ (l1_pre_topc @ X0)
% 6.18/6.40          | ~ (v2_pre_topc @ X0)
% 6.18/6.40          | ~ (v1_xboole_0 @ X1))),
% 6.18/6.40      inference('simplify', [status(thm)], ['4'])).
% 6.18/6.40  thf('6', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i]:
% 6.18/6.40         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 6.18/6.40      inference('sup+', [status(thm)], ['0', '1'])).
% 6.18/6.40  thf(d6_tex_2, axiom,
% 6.18/6.40    (![A:$i]:
% 6.18/6.40     ( ( l1_pre_topc @ A ) =>
% 6.18/6.40       ( ![B:$i]:
% 6.18/6.40         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.18/6.40           ( ( v2_tex_2 @ B @ A ) <=>
% 6.18/6.40             ( ![C:$i]:
% 6.18/6.40               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.18/6.40                 ( ~( ( r1_tarski @ C @ B ) & 
% 6.18/6.40                      ( ![D:$i]:
% 6.18/6.40                        ( ( m1_subset_1 @
% 6.18/6.40                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.18/6.40                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 6.18/6.40                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 6.18/6.40                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 6.18/6.40  thf('7', plain,
% 6.18/6.40      (![X21 : $i, X22 : $i]:
% 6.18/6.40         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 6.18/6.40          | (r1_tarski @ (sk_C @ X21 @ X22) @ X21)
% 6.18/6.40          | (v2_tex_2 @ X21 @ X22)
% 6.18/6.40          | ~ (l1_pre_topc @ X22))),
% 6.18/6.40      inference('cnf', [status(esa)], [d6_tex_2])).
% 6.18/6.40  thf('8', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i]:
% 6.18/6.40         (~ (v1_xboole_0 @ X1)
% 6.18/6.40          | ~ (l1_pre_topc @ X0)
% 6.18/6.40          | (v2_tex_2 @ X1 @ X0)
% 6.18/6.40          | (r1_tarski @ (sk_C @ X1 @ X0) @ X1))),
% 6.18/6.40      inference('sup-', [status(thm)], ['6', '7'])).
% 6.18/6.40  thf('9', plain,
% 6.18/6.40      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.18/6.40      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.18/6.40  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 6.18/6.40  thf('10', plain, (![X9 : $i]: (r1_tarski @ k1_xboole_0 @ X9)),
% 6.18/6.40      inference('cnf', [status(esa)], [t2_xboole_1])).
% 6.18/6.40  thf('11', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 6.18/6.40      inference('sup+', [status(thm)], ['9', '10'])).
% 6.18/6.40  thf(d10_xboole_0, axiom,
% 6.18/6.40    (![A:$i,B:$i]:
% 6.18/6.40     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 6.18/6.40  thf('12', plain,
% 6.18/6.40      (![X1 : $i, X3 : $i]:
% 6.18/6.40         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 6.18/6.40      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.18/6.40  thf('13', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i]:
% 6.18/6.40         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 6.18/6.40      inference('sup-', [status(thm)], ['11', '12'])).
% 6.18/6.40  thf('14', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i]:
% 6.18/6.40         ((v2_tex_2 @ X0 @ X1)
% 6.18/6.40          | ~ (l1_pre_topc @ X1)
% 6.18/6.40          | ~ (v1_xboole_0 @ X0)
% 6.18/6.40          | ((sk_C @ X0 @ X1) = (X0))
% 6.18/6.40          | ~ (v1_xboole_0 @ X0))),
% 6.18/6.40      inference('sup-', [status(thm)], ['8', '13'])).
% 6.18/6.40  thf('15', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i]:
% 6.18/6.40         (((sk_C @ X0 @ X1) = (X0))
% 6.18/6.40          | ~ (v1_xboole_0 @ X0)
% 6.18/6.40          | ~ (l1_pre_topc @ X1)
% 6.18/6.40          | (v2_tex_2 @ X0 @ X1))),
% 6.18/6.40      inference('simplify', [status(thm)], ['14'])).
% 6.18/6.40  thf('16', plain,
% 6.18/6.40      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.18/6.40      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.18/6.40  thf(t35_tex_2, conjecture,
% 6.18/6.40    (![A:$i]:
% 6.18/6.40     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.18/6.40       ( ![B:$i]:
% 6.18/6.40         ( ( ( v1_xboole_0 @ B ) & 
% 6.18/6.40             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 6.18/6.40           ( v2_tex_2 @ B @ A ) ) ) ))).
% 6.18/6.40  thf(zf_stmt_0, negated_conjecture,
% 6.18/6.40    (~( ![A:$i]:
% 6.18/6.40        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 6.18/6.40            ( l1_pre_topc @ A ) ) =>
% 6.18/6.40          ( ![B:$i]:
% 6.18/6.40            ( ( ( v1_xboole_0 @ B ) & 
% 6.18/6.40                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 6.18/6.40              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 6.18/6.40    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 6.18/6.40  thf('17', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 6.18/6.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.40  thf('18', plain, ((v1_xboole_0 @ sk_B)),
% 6.18/6.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.40  thf('19', plain,
% 6.18/6.40      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.18/6.40      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.18/6.40  thf('20', plain, (((sk_B) = (k1_xboole_0))),
% 6.18/6.40      inference('sup-', [status(thm)], ['18', '19'])).
% 6.18/6.40  thf('21', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 6.18/6.40      inference('demod', [status(thm)], ['17', '20'])).
% 6.18/6.40  thf('22', plain,
% 6.18/6.40      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 6.18/6.40      inference('sup-', [status(thm)], ['16', '21'])).
% 6.18/6.40  thf('23', plain,
% 6.18/6.40      (![X0 : $i]:
% 6.18/6.40         (~ (l1_pre_topc @ sk_A)
% 6.18/6.40          | ~ (v1_xboole_0 @ X0)
% 6.18/6.40          | ((sk_C @ X0 @ sk_A) = (X0))
% 6.18/6.40          | ~ (v1_xboole_0 @ X0))),
% 6.18/6.40      inference('sup-', [status(thm)], ['15', '22'])).
% 6.18/6.40  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 6.18/6.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.40  thf('25', plain,
% 6.18/6.40      (![X0 : $i]:
% 6.18/6.40         (~ (v1_xboole_0 @ X0)
% 6.18/6.40          | ((sk_C @ X0 @ sk_A) = (X0))
% 6.18/6.40          | ~ (v1_xboole_0 @ X0))),
% 6.18/6.40      inference('demod', [status(thm)], ['23', '24'])).
% 6.18/6.40  thf('26', plain,
% 6.18/6.40      (![X0 : $i]: (((sk_C @ X0 @ sk_A) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 6.18/6.40      inference('simplify', [status(thm)], ['25'])).
% 6.18/6.40  thf('27', plain,
% 6.18/6.40      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 6.18/6.40      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.18/6.40  thf('28', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 6.18/6.40      inference('simplify', [status(thm)], ['27'])).
% 6.18/6.40  thf(l32_xboole_1, axiom,
% 6.18/6.40    (![A:$i,B:$i]:
% 6.18/6.40     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 6.18/6.40  thf('29', plain,
% 6.18/6.40      (![X4 : $i, X6 : $i]:
% 6.18/6.40         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 6.18/6.40      inference('cnf', [status(esa)], [l32_xboole_1])).
% 6.18/6.40  thf('30', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 6.18/6.40      inference('sup-', [status(thm)], ['28', '29'])).
% 6.18/6.40  thf('31', plain,
% 6.18/6.40      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.18/6.40      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.18/6.40  thf('32', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i]:
% 6.18/6.40         (~ (v1_xboole_0 @ X1)
% 6.18/6.40          | ~ (l1_pre_topc @ X0)
% 6.18/6.40          | (v2_tex_2 @ X1 @ X0)
% 6.18/6.40          | (r1_tarski @ (sk_C @ X1 @ X0) @ X1))),
% 6.18/6.40      inference('sup-', [status(thm)], ['6', '7'])).
% 6.18/6.40  thf('33', plain, (![X9 : $i]: (r1_tarski @ k1_xboole_0 @ X9)),
% 6.18/6.40      inference('cnf', [status(esa)], [t2_xboole_1])).
% 6.18/6.40  thf('34', plain,
% 6.18/6.40      (![X1 : $i, X3 : $i]:
% 6.18/6.40         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 6.18/6.40      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.18/6.40  thf('35', plain,
% 6.18/6.40      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 6.18/6.40      inference('sup-', [status(thm)], ['33', '34'])).
% 6.18/6.40  thf('36', plain,
% 6.18/6.40      (![X0 : $i]:
% 6.18/6.40         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 6.18/6.40          | ~ (l1_pre_topc @ X0)
% 6.18/6.40          | ~ (v1_xboole_0 @ k1_xboole_0)
% 6.18/6.40          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 6.18/6.40      inference('sup-', [status(thm)], ['32', '35'])).
% 6.18/6.40  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 6.18/6.40  thf('37', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.18/6.40      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.18/6.40  thf('38', plain,
% 6.18/6.40      (![X0 : $i]:
% 6.18/6.40         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 6.18/6.40          | ~ (l1_pre_topc @ X0)
% 6.18/6.40          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 6.18/6.40      inference('demod', [status(thm)], ['36', '37'])).
% 6.18/6.40  thf('39', plain,
% 6.18/6.40      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 6.18/6.40      inference('sup-', [status(thm)], ['16', '21'])).
% 6.18/6.40  thf('40', plain,
% 6.18/6.40      ((((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))
% 6.18/6.40        | ~ (l1_pre_topc @ sk_A)
% 6.18/6.40        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 6.18/6.40      inference('sup-', [status(thm)], ['38', '39'])).
% 6.18/6.40  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 6.18/6.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.40  thf('42', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.18/6.40      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.18/6.40  thf('43', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 6.18/6.40      inference('demod', [status(thm)], ['40', '41', '42'])).
% 6.18/6.40  thf('44', plain,
% 6.18/6.40      (![X0 : $i]:
% 6.18/6.40         (((sk_C @ X0 @ sk_A) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.18/6.40      inference('sup+', [status(thm)], ['31', '43'])).
% 6.18/6.40  thf('45', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i]:
% 6.18/6.40         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 6.18/6.40      inference('sup+', [status(thm)], ['0', '1'])).
% 6.18/6.40  thf('46', plain,
% 6.18/6.40      (![X21 : $i, X22 : $i]:
% 6.18/6.40         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 6.18/6.40          | (m1_subset_1 @ (sk_C @ X21 @ X22) @ 
% 6.18/6.40             (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 6.18/6.40          | (v2_tex_2 @ X21 @ X22)
% 6.18/6.40          | ~ (l1_pre_topc @ X22))),
% 6.18/6.40      inference('cnf', [status(esa)], [d6_tex_2])).
% 6.18/6.40  thf('47', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i]:
% 6.18/6.40         (~ (v1_xboole_0 @ X1)
% 6.18/6.40          | ~ (l1_pre_topc @ X0)
% 6.18/6.40          | (v2_tex_2 @ X1 @ X0)
% 6.18/6.40          | (m1_subset_1 @ (sk_C @ X1 @ X0) @ 
% 6.18/6.40             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 6.18/6.40      inference('sup-', [status(thm)], ['45', '46'])).
% 6.18/6.40  thf(redefinition_k9_subset_1, axiom,
% 6.18/6.40    (![A:$i,B:$i,C:$i]:
% 6.18/6.40     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 6.18/6.40       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 6.18/6.40  thf('48', plain,
% 6.18/6.40      (![X12 : $i, X13 : $i, X14 : $i]:
% 6.18/6.40         (((k9_subset_1 @ X14 @ X12 @ X13) = (k3_xboole_0 @ X12 @ X13))
% 6.18/6.40          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 6.18/6.40      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 6.18/6.40  thf('49', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.18/6.40         ((v2_tex_2 @ X1 @ X0)
% 6.18/6.40          | ~ (l1_pre_topc @ X0)
% 6.18/6.40          | ~ (v1_xboole_0 @ X1)
% 6.18/6.40          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ X2 @ (sk_C @ X1 @ X0))
% 6.18/6.40              = (k3_xboole_0 @ X2 @ (sk_C @ X1 @ X0))))),
% 6.18/6.40      inference('sup-', [status(thm)], ['47', '48'])).
% 6.18/6.40  thf('50', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i]:
% 6.18/6.40         (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X1 @ k1_xboole_0)
% 6.18/6.40            = (k3_xboole_0 @ X1 @ (sk_C @ X0 @ sk_A)))
% 6.18/6.40          | ~ (v1_xboole_0 @ X0)
% 6.18/6.40          | ~ (v1_xboole_0 @ X0)
% 6.18/6.40          | ~ (l1_pre_topc @ sk_A)
% 6.18/6.40          | (v2_tex_2 @ X0 @ sk_A))),
% 6.18/6.40      inference('sup+', [status(thm)], ['44', '49'])).
% 6.18/6.40  thf('51', plain,
% 6.18/6.40      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 6.18/6.40      inference('cnf', [status(esa)], [t4_subset_1])).
% 6.18/6.40  thf('52', plain,
% 6.18/6.40      (![X12 : $i, X13 : $i, X14 : $i]:
% 6.18/6.40         (((k9_subset_1 @ X14 @ X12 @ X13) = (k3_xboole_0 @ X12 @ X13))
% 6.18/6.40          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 6.18/6.40      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 6.18/6.40  thf('53', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i]:
% 6.18/6.40         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 6.18/6.40           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 6.18/6.40      inference('sup-', [status(thm)], ['51', '52'])).
% 6.18/6.40  thf('54', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 6.18/6.40      inference('sup-', [status(thm)], ['28', '29'])).
% 6.18/6.40  thf(t48_xboole_1, axiom,
% 6.18/6.40    (![A:$i,B:$i]:
% 6.18/6.40     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 6.18/6.40  thf('55', plain,
% 6.18/6.40      (![X10 : $i, X11 : $i]:
% 6.18/6.40         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 6.18/6.40           = (k3_xboole_0 @ X10 @ X11))),
% 6.18/6.40      inference('cnf', [status(esa)], [t48_xboole_1])).
% 6.18/6.40  thf('56', plain,
% 6.18/6.40      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 6.18/6.40      inference('sup+', [status(thm)], ['54', '55'])).
% 6.18/6.40  thf('57', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 6.18/6.40      inference('simplify', [status(thm)], ['27'])).
% 6.18/6.40  thf(t28_xboole_1, axiom,
% 6.18/6.40    (![A:$i,B:$i]:
% 6.18/6.40     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 6.18/6.40  thf('58', plain,
% 6.18/6.40      (![X7 : $i, X8 : $i]:
% 6.18/6.40         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 6.18/6.40      inference('cnf', [status(esa)], [t28_xboole_1])).
% 6.18/6.40  thf('59', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 6.18/6.40      inference('sup-', [status(thm)], ['57', '58'])).
% 6.18/6.40  thf('60', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 6.18/6.40      inference('demod', [status(thm)], ['56', '59'])).
% 6.18/6.40  thf('61', plain,
% 6.18/6.40      (![X10 : $i, X11 : $i]:
% 6.18/6.40         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 6.18/6.40           = (k3_xboole_0 @ X10 @ X11))),
% 6.18/6.40      inference('cnf', [status(esa)], [t48_xboole_1])).
% 6.18/6.40  thf('62', plain,
% 6.18/6.40      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 6.18/6.40      inference('sup+', [status(thm)], ['60', '61'])).
% 6.18/6.40  thf('63', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 6.18/6.40      inference('sup-', [status(thm)], ['28', '29'])).
% 6.18/6.40  thf('64', plain,
% 6.18/6.40      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 6.18/6.40      inference('demod', [status(thm)], ['62', '63'])).
% 6.18/6.40  thf('65', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i]:
% 6.18/6.40         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 6.18/6.40      inference('demod', [status(thm)], ['53', '64'])).
% 6.18/6.40  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 6.18/6.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.40  thf('67', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i]:
% 6.18/6.40         (((k1_xboole_0) = (k3_xboole_0 @ X1 @ (sk_C @ X0 @ sk_A)))
% 6.18/6.40          | ~ (v1_xboole_0 @ X0)
% 6.18/6.40          | ~ (v1_xboole_0 @ X0)
% 6.18/6.40          | (v2_tex_2 @ X0 @ sk_A))),
% 6.18/6.40      inference('demod', [status(thm)], ['50', '65', '66'])).
% 6.18/6.40  thf('68', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i]:
% 6.18/6.40         ((v2_tex_2 @ X0 @ sk_A)
% 6.18/6.40          | ~ (v1_xboole_0 @ X0)
% 6.18/6.40          | ((k1_xboole_0) = (k3_xboole_0 @ X1 @ (sk_C @ X0 @ sk_A))))),
% 6.18/6.40      inference('simplify', [status(thm)], ['67'])).
% 6.18/6.40  thf('69', plain,
% 6.18/6.40      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 6.18/6.40      inference('sup-', [status(thm)], ['16', '21'])).
% 6.18/6.40  thf('70', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i]:
% 6.18/6.40         (((k1_xboole_0) = (k3_xboole_0 @ X1 @ (sk_C @ X0 @ sk_A)))
% 6.18/6.40          | ~ (v1_xboole_0 @ X0))),
% 6.18/6.40      inference('clc', [status(thm)], ['68', '69'])).
% 6.18/6.40  thf('71', plain,
% 6.18/6.40      (![X10 : $i, X11 : $i]:
% 6.18/6.40         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 6.18/6.40           = (k3_xboole_0 @ X10 @ X11))),
% 6.18/6.40      inference('cnf', [status(esa)], [t48_xboole_1])).
% 6.18/6.40  thf('72', plain,
% 6.18/6.40      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.18/6.40      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.18/6.40  thf('73', plain,
% 6.18/6.40      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 6.18/6.40      inference('demod', [status(thm)], ['62', '63'])).
% 6.18/6.40  thf('74', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i]:
% 6.18/6.40         (((k1_xboole_0) = (k3_xboole_0 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 6.18/6.40      inference('sup+', [status(thm)], ['72', '73'])).
% 6.18/6.40  thf('75', plain,
% 6.18/6.40      (![X10 : $i, X11 : $i]:
% 6.18/6.40         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 6.18/6.40           = (k3_xboole_0 @ X10 @ X11))),
% 6.18/6.40      inference('cnf', [status(esa)], [t48_xboole_1])).
% 6.18/6.40  thf('76', plain,
% 6.18/6.40      (![X4 : $i, X5 : $i]:
% 6.18/6.40         ((r1_tarski @ X4 @ X5) | ((k4_xboole_0 @ X4 @ X5) != (k1_xboole_0)))),
% 6.18/6.40      inference('cnf', [status(esa)], [l32_xboole_1])).
% 6.18/6.40  thf('77', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i]:
% 6.18/6.40         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 6.18/6.40          | (r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 6.18/6.40      inference('sup-', [status(thm)], ['75', '76'])).
% 6.18/6.40  thf('78', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i]:
% 6.18/6.40         (((k1_xboole_0) != (k1_xboole_0))
% 6.18/6.40          | ~ (v1_xboole_0 @ X0)
% 6.18/6.40          | (r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 6.18/6.40      inference('sup-', [status(thm)], ['74', '77'])).
% 6.18/6.40  thf('79', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i]:
% 6.18/6.40         ((r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 6.18/6.40      inference('simplify', [status(thm)], ['78'])).
% 6.18/6.40  thf('80', plain,
% 6.18/6.40      (![X7 : $i, X8 : $i]:
% 6.18/6.40         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 6.18/6.40      inference('cnf', [status(esa)], [t28_xboole_1])).
% 6.18/6.40  thf('81', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i]:
% 6.18/6.40         (~ (v1_xboole_0 @ X0)
% 6.18/6.40          | ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1)))),
% 6.18/6.40      inference('sup-', [status(thm)], ['79', '80'])).
% 6.18/6.40  thf('82', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i]:
% 6.18/6.40         (((k1_xboole_0) = (k3_xboole_0 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 6.18/6.40      inference('sup+', [status(thm)], ['72', '73'])).
% 6.18/6.40  thf('83', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.18/6.40      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.18/6.40  thf('84', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i]:
% 6.18/6.40         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 6.18/6.40      inference('sup+', [status(thm)], ['82', '83'])).
% 6.18/6.40  thf('85', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i]:
% 6.18/6.40         ((v1_xboole_0 @ X0)
% 6.18/6.40          | ~ (v1_xboole_0 @ X1)
% 6.18/6.40          | ~ (v1_xboole_0 @ (k4_xboole_0 @ X0 @ X1)))),
% 6.18/6.40      inference('sup+', [status(thm)], ['81', '84'])).
% 6.18/6.40  thf('86', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i]:
% 6.18/6.40         (~ (v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0))
% 6.18/6.40          | ~ (v1_xboole_0 @ (k4_xboole_0 @ X1 @ X0))
% 6.18/6.40          | (v1_xboole_0 @ X1))),
% 6.18/6.40      inference('sup-', [status(thm)], ['71', '85'])).
% 6.18/6.40  thf('87', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i]:
% 6.18/6.40         (~ (v1_xboole_0 @ k1_xboole_0)
% 6.18/6.40          | ~ (v1_xboole_0 @ X0)
% 6.18/6.40          | (v1_xboole_0 @ X1)
% 6.18/6.40          | ~ (v1_xboole_0 @ (k4_xboole_0 @ X1 @ (sk_C @ X0 @ sk_A))))),
% 6.18/6.40      inference('sup-', [status(thm)], ['70', '86'])).
% 6.18/6.40  thf('88', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.18/6.40      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.18/6.40  thf('89', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i]:
% 6.18/6.40         (~ (v1_xboole_0 @ X0)
% 6.18/6.40          | (v1_xboole_0 @ X1)
% 6.18/6.40          | ~ (v1_xboole_0 @ (k4_xboole_0 @ X1 @ (sk_C @ X0 @ sk_A))))),
% 6.18/6.40      inference('demod', [status(thm)], ['87', '88'])).
% 6.18/6.40  thf('90', plain,
% 6.18/6.40      (![X0 : $i]:
% 6.18/6.40         (~ (v1_xboole_0 @ k1_xboole_0)
% 6.18/6.40          | (v1_xboole_0 @ (sk_C @ X0 @ sk_A))
% 6.18/6.40          | ~ (v1_xboole_0 @ X0))),
% 6.18/6.40      inference('sup-', [status(thm)], ['30', '89'])).
% 6.18/6.40  thf('91', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.18/6.40      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.18/6.40  thf('92', plain,
% 6.18/6.40      (![X0 : $i]: ((v1_xboole_0 @ (sk_C @ X0 @ sk_A)) | ~ (v1_xboole_0 @ X0))),
% 6.18/6.40      inference('demod', [status(thm)], ['90', '91'])).
% 6.18/6.40  thf('93', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 6.18/6.40      inference('sup+', [status(thm)], ['9', '10'])).
% 6.18/6.40  thf('94', plain,
% 6.18/6.40      (![X7 : $i, X8 : $i]:
% 6.18/6.40         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 6.18/6.40      inference('cnf', [status(esa)], [t28_xboole_1])).
% 6.18/6.40  thf('95', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i]:
% 6.18/6.40         (~ (v1_xboole_0 @ X1) | ((k3_xboole_0 @ X1 @ X0) = (X1)))),
% 6.18/6.40      inference('sup-', [status(thm)], ['93', '94'])).
% 6.18/6.40  thf('96', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i]:
% 6.18/6.40         (~ (v1_xboole_0 @ X0)
% 6.18/6.40          | ((k3_xboole_0 @ (sk_C @ X0 @ sk_A) @ X1) = (sk_C @ X0 @ sk_A)))),
% 6.18/6.40      inference('sup-', [status(thm)], ['92', '95'])).
% 6.18/6.40  thf('97', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i]:
% 6.18/6.40         (((k3_xboole_0 @ X0 @ X1) = (sk_C @ X0 @ sk_A))
% 6.18/6.40          | ~ (v1_xboole_0 @ X0)
% 6.18/6.40          | ~ (v1_xboole_0 @ X0))),
% 6.18/6.40      inference('sup+', [status(thm)], ['26', '96'])).
% 6.18/6.40  thf('98', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i]:
% 6.18/6.40         (~ (v1_xboole_0 @ X0) | ((k3_xboole_0 @ X0 @ X1) = (sk_C @ X0 @ sk_A)))),
% 6.18/6.40      inference('simplify', [status(thm)], ['97'])).
% 6.18/6.40  thf('99', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i]:
% 6.18/6.40         (~ (v1_xboole_0 @ X1) | ((k3_xboole_0 @ X1 @ X0) = (X1)))),
% 6.18/6.40      inference('sup-', [status(thm)], ['93', '94'])).
% 6.18/6.40  thf('100', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i]:
% 6.18/6.40         (~ (v1_xboole_0 @ X1) | ((k3_xboole_0 @ X1 @ X0) = (X1)))),
% 6.18/6.40      inference('sup-', [status(thm)], ['93', '94'])).
% 6.18/6.40  thf('101', plain,
% 6.18/6.40      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.18/6.40      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.18/6.40  thf('102', plain, (![X9 : $i]: (r1_tarski @ k1_xboole_0 @ X9)),
% 6.18/6.40      inference('cnf', [status(esa)], [t2_xboole_1])).
% 6.18/6.40  thf('103', plain,
% 6.18/6.40      (![X7 : $i, X8 : $i]:
% 6.18/6.40         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 6.18/6.40      inference('cnf', [status(esa)], [t28_xboole_1])).
% 6.18/6.40  thf('104', plain,
% 6.18/6.40      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 6.18/6.40      inference('sup-', [status(thm)], ['102', '103'])).
% 6.18/6.40  thf('105', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i]:
% 6.18/6.40         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.18/6.40      inference('sup+', [status(thm)], ['101', '104'])).
% 6.18/6.40  thf('106', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.18/6.40      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.18/6.40  thf('107', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i]:
% 6.18/6.40         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (v1_xboole_0 @ X1))),
% 6.18/6.40      inference('sup+', [status(thm)], ['105', '106'])).
% 6.18/6.40  thf('108', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i]:
% 6.18/6.40         (~ (v1_xboole_0 @ X1) | ((k3_xboole_0 @ X1 @ X0) = (X1)))),
% 6.18/6.40      inference('sup-', [status(thm)], ['93', '94'])).
% 6.18/6.40  thf('109', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.18/6.40         (~ (v1_xboole_0 @ X1)
% 6.18/6.40          | ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 6.18/6.40              = (k3_xboole_0 @ X1 @ X0)))),
% 6.18/6.40      inference('sup-', [status(thm)], ['107', '108'])).
% 6.18/6.40  thf('110', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.18/6.40         (((k3_xboole_0 @ X0 @ X2) = (k3_xboole_0 @ X0 @ X1))
% 6.18/6.40          | ~ (v1_xboole_0 @ X0)
% 6.18/6.40          | ~ (v1_xboole_0 @ X0))),
% 6.18/6.40      inference('sup+', [status(thm)], ['100', '109'])).
% 6.18/6.40  thf('111', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.18/6.40         (~ (v1_xboole_0 @ X0)
% 6.18/6.40          | ((k3_xboole_0 @ X0 @ X2) = (k3_xboole_0 @ X0 @ X1)))),
% 6.18/6.40      inference('simplify', [status(thm)], ['110'])).
% 6.18/6.40  thf('112', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i]:
% 6.18/6.40         (~ (v1_xboole_0 @ X1) | ((k3_xboole_0 @ X1 @ X0) = (X1)))),
% 6.18/6.40      inference('sup-', [status(thm)], ['93', '94'])).
% 6.18/6.40  thf('113', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i]:
% 6.18/6.40         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.18/6.40      inference('sup+', [status(thm)], ['101', '104'])).
% 6.18/6.40  thf('114', plain,
% 6.18/6.40      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 6.18/6.40      inference('cnf', [status(esa)], [t4_subset_1])).
% 6.18/6.40  thf('115', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.18/6.40         ((m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X2))
% 6.18/6.40          | ~ (v1_xboole_0 @ X1))),
% 6.18/6.40      inference('sup+', [status(thm)], ['113', '114'])).
% 6.18/6.40  thf('116', plain,
% 6.18/6.40      (![X12 : $i, X13 : $i, X14 : $i]:
% 6.18/6.40         (((k9_subset_1 @ X14 @ X12 @ X13) = (k3_xboole_0 @ X12 @ X13))
% 6.18/6.40          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 6.18/6.40      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 6.18/6.40  thf('117', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.18/6.40         (~ (v1_xboole_0 @ X2)
% 6.18/6.40          | ((k9_subset_1 @ X0 @ X3 @ (k3_xboole_0 @ X2 @ X1))
% 6.18/6.40              = (k3_xboole_0 @ X3 @ (k3_xboole_0 @ X2 @ X1))))),
% 6.18/6.40      inference('sup-', [status(thm)], ['115', '116'])).
% 6.18/6.40  thf('118', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.18/6.40         (((k9_subset_1 @ X3 @ X2 @ X0)
% 6.18/6.40            = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1)))
% 6.18/6.40          | ~ (v1_xboole_0 @ X0)
% 6.18/6.40          | ~ (v1_xboole_0 @ X0))),
% 6.18/6.40      inference('sup+', [status(thm)], ['112', '117'])).
% 6.18/6.40  thf('119', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.18/6.40         (~ (v1_xboole_0 @ X0)
% 6.18/6.40          | ((k9_subset_1 @ X3 @ X2 @ X0)
% 6.18/6.40              = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1))))),
% 6.18/6.40      inference('simplify', [status(thm)], ['118'])).
% 6.18/6.40  thf('120', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 6.18/6.40      inference('sup-', [status(thm)], ['57', '58'])).
% 6.18/6.40  thf('121', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.18/6.40         (((k9_subset_1 @ X2 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 6.18/6.40            = (k3_xboole_0 @ X0 @ X1))
% 6.18/6.40          | ~ (v1_xboole_0 @ X0))),
% 6.18/6.40      inference('sup+', [status(thm)], ['119', '120'])).
% 6.18/6.40  thf('122', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.18/6.40         (((k9_subset_1 @ X3 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 6.18/6.40            = (k3_xboole_0 @ X1 @ X2))
% 6.18/6.40          | ~ (v1_xboole_0 @ X1)
% 6.18/6.40          | ~ (v1_xboole_0 @ X1))),
% 6.18/6.40      inference('sup+', [status(thm)], ['111', '121'])).
% 6.18/6.40  thf('123', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.18/6.40         (~ (v1_xboole_0 @ X1)
% 6.18/6.40          | ((k9_subset_1 @ X3 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 6.18/6.40              = (k3_xboole_0 @ X1 @ X2)))),
% 6.18/6.40      inference('simplify', [status(thm)], ['122'])).
% 6.18/6.40  thf('124', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.18/6.40         (((k9_subset_1 @ X2 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))
% 6.18/6.40          | ~ (v1_xboole_0 @ X0)
% 6.18/6.40          | ~ (v1_xboole_0 @ X0))),
% 6.18/6.40      inference('sup+', [status(thm)], ['99', '123'])).
% 6.18/6.40  thf('125', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.18/6.40         (~ (v1_xboole_0 @ X0)
% 6.18/6.40          | ((k9_subset_1 @ X2 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0)))),
% 6.18/6.40      inference('simplify', [status(thm)], ['124'])).
% 6.18/6.40  thf('126', plain,
% 6.18/6.40      (![X0 : $i, X2 : $i]:
% 6.18/6.40         (((k9_subset_1 @ X2 @ (sk_C @ X0 @ sk_A) @ X0) = (X0))
% 6.18/6.40          | ~ (v1_xboole_0 @ X0)
% 6.18/6.40          | ~ (v1_xboole_0 @ X0))),
% 6.18/6.40      inference('sup+', [status(thm)], ['98', '125'])).
% 6.18/6.40  thf('127', plain,
% 6.18/6.40      (![X0 : $i, X2 : $i]:
% 6.18/6.40         (~ (v1_xboole_0 @ X0)
% 6.18/6.40          | ((k9_subset_1 @ X2 @ (sk_C @ X0 @ sk_A) @ X0) = (X0)))),
% 6.18/6.40      inference('simplify', [status(thm)], ['126'])).
% 6.18/6.40  thf('128', plain,
% 6.18/6.40      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 6.18/6.40      inference('cnf', [status(esa)], [t4_subset_1])).
% 6.18/6.40  thf('129', plain,
% 6.18/6.40      (![X21 : $i, X22 : $i]:
% 6.18/6.40         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 6.18/6.40          | (m1_subset_1 @ (sk_C @ X21 @ X22) @ 
% 6.18/6.40             (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 6.18/6.40          | (v2_tex_2 @ X21 @ X22)
% 6.18/6.40          | ~ (l1_pre_topc @ X22))),
% 6.18/6.40      inference('cnf', [status(esa)], [d6_tex_2])).
% 6.18/6.40  thf('130', plain,
% 6.18/6.40      (![X0 : $i]:
% 6.18/6.40         (~ (l1_pre_topc @ X0)
% 6.18/6.40          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 6.18/6.40          | (m1_subset_1 @ (sk_C @ k1_xboole_0 @ X0) @ 
% 6.18/6.40             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 6.18/6.40      inference('sup-', [status(thm)], ['128', '129'])).
% 6.18/6.40  thf('131', plain,
% 6.18/6.40      (![X21 : $i, X22 : $i, X24 : $i]:
% 6.18/6.40         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 6.18/6.40          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 6.18/6.40          | ~ (v4_pre_topc @ X24 @ X22)
% 6.18/6.40          | ((k9_subset_1 @ (u1_struct_0 @ X22) @ X21 @ X24)
% 6.18/6.40              != (sk_C @ X21 @ X22))
% 6.18/6.40          | (v2_tex_2 @ X21 @ X22)
% 6.18/6.40          | ~ (l1_pre_topc @ X22))),
% 6.18/6.40      inference('cnf', [status(esa)], [d6_tex_2])).
% 6.18/6.40  thf('132', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i]:
% 6.18/6.40         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 6.18/6.40          | ~ (l1_pre_topc @ X0)
% 6.18/6.40          | ~ (l1_pre_topc @ X0)
% 6.18/6.40          | (v2_tex_2 @ (sk_C @ k1_xboole_0 @ X0) @ X0)
% 6.18/6.40          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ (sk_C @ k1_xboole_0 @ X0) @ X1)
% 6.18/6.40              != (sk_C @ (sk_C @ k1_xboole_0 @ X0) @ X0))
% 6.18/6.40          | ~ (v4_pre_topc @ X1 @ X0)
% 6.18/6.40          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 6.18/6.40      inference('sup-', [status(thm)], ['130', '131'])).
% 6.18/6.40  thf('133', plain,
% 6.18/6.40      (![X0 : $i, X1 : $i]:
% 6.18/6.40         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 6.18/6.40          | ~ (v4_pre_topc @ X1 @ X0)
% 6.18/6.40          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ (sk_C @ k1_xboole_0 @ X0) @ X1)
% 6.18/6.40              != (sk_C @ (sk_C @ k1_xboole_0 @ X0) @ X0))
% 6.18/6.40          | (v2_tex_2 @ (sk_C @ k1_xboole_0 @ X0) @ X0)
% 6.18/6.40          | ~ (l1_pre_topc @ X0)
% 6.18/6.40          | (v2_tex_2 @ k1_xboole_0 @ X0))),
% 6.18/6.40      inference('simplify', [status(thm)], ['132'])).
% 6.18/6.40  thf('134', plain,
% 6.18/6.40      ((((k1_xboole_0) != (sk_C @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_A))
% 6.18/6.40        | ~ (v1_xboole_0 @ k1_xboole_0)
% 6.18/6.40        | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 6.18/6.40        | ~ (l1_pre_topc @ sk_A)
% 6.18/6.40        | (v2_tex_2 @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_A)
% 6.18/6.40        | ~ (v4_pre_topc @ k1_xboole_0 @ sk_A)
% 6.18/6.40        | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 6.18/6.40      inference('sup-', [status(thm)], ['127', '133'])).
% 6.18/6.40  thf('135', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 6.18/6.40      inference('demod', [status(thm)], ['40', '41', '42'])).
% 6.18/6.40  thf('136', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 6.18/6.40      inference('demod', [status(thm)], ['40', '41', '42'])).
% 6.18/6.40  thf('137', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.18/6.40      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.18/6.40  thf('138', plain, ((l1_pre_topc @ sk_A)),
% 6.18/6.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.40  thf('139', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 6.18/6.40      inference('demod', [status(thm)], ['40', '41', '42'])).
% 6.18/6.40  thf('140', plain,
% 6.18/6.40      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 6.18/6.40      inference('cnf', [status(esa)], [t4_subset_1])).
% 6.18/6.40  thf('141', plain,
% 6.18/6.40      ((((k1_xboole_0) != (k1_xboole_0))
% 6.18/6.40        | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 6.18/6.40        | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 6.18/6.40        | ~ (v4_pre_topc @ k1_xboole_0 @ sk_A))),
% 6.18/6.40      inference('demod', [status(thm)],
% 6.18/6.40                ['134', '135', '136', '137', '138', '139', '140'])).
% 6.18/6.40  thf('142', plain,
% 6.18/6.40      ((~ (v4_pre_topc @ k1_xboole_0 @ sk_A) | (v2_tex_2 @ k1_xboole_0 @ sk_A))),
% 6.18/6.40      inference('simplify', [status(thm)], ['141'])).
% 6.18/6.40  thf('143', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 6.18/6.40      inference('demod', [status(thm)], ['17', '20'])).
% 6.18/6.40  thf('144', plain, (~ (v4_pre_topc @ k1_xboole_0 @ sk_A)),
% 6.18/6.40      inference('clc', [status(thm)], ['142', '143'])).
% 6.18/6.40  thf('145', plain,
% 6.18/6.40      ((~ (v1_xboole_0 @ k1_xboole_0)
% 6.18/6.40        | ~ (v2_pre_topc @ sk_A)
% 6.18/6.40        | ~ (l1_pre_topc @ sk_A))),
% 6.18/6.40      inference('sup-', [status(thm)], ['5', '144'])).
% 6.18/6.40  thf('146', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.18/6.40      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.18/6.40  thf('147', plain, ((v2_pre_topc @ sk_A)),
% 6.18/6.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.40  thf('148', plain, ((l1_pre_topc @ sk_A)),
% 6.18/6.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.18/6.40  thf('149', plain, ($false),
% 6.18/6.40      inference('demod', [status(thm)], ['145', '146', '147', '148'])).
% 6.18/6.40  
% 6.18/6.40  % SZS output end Refutation
% 6.18/6.40  
% 6.18/6.40  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
