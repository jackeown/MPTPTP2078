%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KMnk2CBEQ7

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 137 expanded)
%              Number of leaves         :   33 (  55 expanded)
%              Depth                    :   15
%              Number of atoms          :  582 (1047 expanded)
%              Number of equality atoms :   41 (  54 expanded)
%              Maximal formula depth    :   19 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('3',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('6',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

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

thf('8',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( r1_tarski @ ( sk_C @ X21 @ X22 ) @ X21 )
      | ( v2_tex_2 @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ X1 @ X0 )
      | ( r1_tarski @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_tex_2 @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( sk_C @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_tex_2 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( sk_C @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

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
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(fc4_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('23',plain,(
    ! [X20: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X20 ) @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc4_pre_topc])).

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
      | ~ ( v4_pre_topc @ X24 @ X22 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X22 ) @ X21 @ X24 )
       != ( sk_C @ X21 @ X22 ) )
      | ( v2_tex_2 @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ X1 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v4_pre_topc @ X1 @ X0 )
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

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('38',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k9_subset_1 @ X0 @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['33','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v4_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['30','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
       != ( sk_C @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_tex_2 @ k1_xboole_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','48'])).

thf('50',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('52',plain,(
    ! [X19: $i] :
      ( ( l1_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('53',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['18','19'])).

thf('57',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['50','53','54','55','56'])).

thf('58',plain,(
    v2_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['4','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KMnk2CBEQ7
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:54:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.58  % Solved by: fo/fo7.sh
% 0.21/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.58  % done 210 iterations in 0.116s
% 0.21/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.58  % SZS output start Refutation
% 0.21/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.58  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.58  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.21/0.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.58  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.21/0.58  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.21/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.58  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.58  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.58  thf(t35_tex_2, conjecture,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.58       ( ![B:$i]:
% 0.21/0.58         ( ( ( v1_xboole_0 @ B ) & 
% 0.21/0.58             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.58           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.21/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.58    (~( ![A:$i]:
% 0.21/0.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.58            ( l1_pre_topc @ A ) ) =>
% 0.21/0.58          ( ![B:$i]:
% 0.21/0.58            ( ( ( v1_xboole_0 @ B ) & 
% 0.21/0.58                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.58              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.21/0.58    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 0.21/0.58  thf('0', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('1', plain, ((v1_xboole_0 @ sk_B)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(l13_xboole_0, axiom,
% 0.21/0.58    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.58  thf('2', plain,
% 0.21/0.58      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 0.21/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.58  thf('3', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.58  thf('4', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.21/0.58      inference('demod', [status(thm)], ['0', '3'])).
% 0.21/0.58  thf('5', plain,
% 0.21/0.58      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 0.21/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.58  thf(t4_subset_1, axiom,
% 0.21/0.58    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.58  thf('6', plain,
% 0.21/0.58      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 0.21/0.58      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.58  thf('7', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.58      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.58  thf(d6_tex_2, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( l1_pre_topc @ A ) =>
% 0.21/0.58       ( ![B:$i]:
% 0.21/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.58           ( ( v2_tex_2 @ B @ A ) <=>
% 0.21/0.58             ( ![C:$i]:
% 0.21/0.58               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.58                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.21/0.58                      ( ![D:$i]:
% 0.21/0.58                        ( ( m1_subset_1 @
% 0.21/0.58                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.58                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.21/0.58                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.21/0.58                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.58  thf('8', plain,
% 0.21/0.58      (![X21 : $i, X22 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.21/0.58          | (r1_tarski @ (sk_C @ X21 @ X22) @ X21)
% 0.21/0.58          | (v2_tex_2 @ X21 @ X22)
% 0.21/0.58          | ~ (l1_pre_topc @ X22))),
% 0.21/0.58      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.21/0.58  thf('9', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (~ (v1_xboole_0 @ X1)
% 0.21/0.58          | ~ (l1_pre_topc @ X0)
% 0.21/0.58          | (v2_tex_2 @ X1 @ X0)
% 0.21/0.58          | (r1_tarski @ (sk_C @ X1 @ X0) @ X1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.58  thf('10', plain,
% 0.21/0.58      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 0.21/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.58  thf(t3_xboole_1, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.58  thf('11', plain,
% 0.21/0.58      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ k1_xboole_0))),
% 0.21/0.58      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.21/0.58  thf('12', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (~ (r1_tarski @ X1 @ X0)
% 0.21/0.58          | ~ (v1_xboole_0 @ X0)
% 0.21/0.58          | ((X1) = (k1_xboole_0)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.58  thf('13', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         ((v2_tex_2 @ X0 @ X1)
% 0.21/0.58          | ~ (l1_pre_topc @ X1)
% 0.21/0.58          | ~ (v1_xboole_0 @ X0)
% 0.21/0.58          | ((sk_C @ X0 @ X1) = (k1_xboole_0))
% 0.21/0.58          | ~ (v1_xboole_0 @ X0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['9', '12'])).
% 0.21/0.58  thf('14', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (((sk_C @ X0 @ X1) = (k1_xboole_0))
% 0.21/0.58          | ~ (v1_xboole_0 @ X0)
% 0.21/0.58          | ~ (l1_pre_topc @ X1)
% 0.21/0.58          | (v2_tex_2 @ X0 @ X1))),
% 0.21/0.58      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.58  thf('15', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.21/0.58      inference('demod', [status(thm)], ['0', '3'])).
% 0.21/0.58  thf('16', plain,
% 0.21/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.58        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.58        | ((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.58  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('18', plain, ((v1_xboole_0 @ sk_B)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('19', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.58  thf('20', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.58      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.58  thf('21', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.21/0.58      inference('demod', [status(thm)], ['16', '17', '20'])).
% 0.21/0.58  thf('22', plain,
% 0.21/0.58      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 0.21/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.58  thf(fc4_pre_topc, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.58       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.21/0.58  thf('23', plain,
% 0.21/0.58      (![X20 : $i]:
% 0.21/0.58         ((v4_pre_topc @ (k2_struct_0 @ X20) @ X20)
% 0.21/0.58          | ~ (l1_pre_topc @ X20)
% 0.21/0.58          | ~ (v2_pre_topc @ X20))),
% 0.21/0.58      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.21/0.58  thf(d3_struct_0, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.58  thf('24', plain,
% 0.21/0.58      (![X18 : $i]:
% 0.21/0.58         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.58  thf(dt_k2_subset_1, axiom,
% 0.21/0.58    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.58  thf('25', plain,
% 0.21/0.58      (![X10 : $i]: (m1_subset_1 @ (k2_subset_1 @ X10) @ (k1_zfmisc_1 @ X10))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.21/0.58  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.21/0.58  thf('26', plain, (![X9 : $i]: ((k2_subset_1 @ X9) = (X9))),
% 0.21/0.58      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.58  thf('27', plain, (![X10 : $i]: (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X10))),
% 0.21/0.58      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.58  thf('28', plain,
% 0.21/0.58      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 0.21/0.58      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.58  thf('29', plain,
% 0.21/0.58      (![X21 : $i, X22 : $i, X24 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.21/0.58          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.21/0.58          | ~ (v4_pre_topc @ X24 @ X22)
% 0.21/0.58          | ((k9_subset_1 @ (u1_struct_0 @ X22) @ X21 @ X24)
% 0.21/0.58              != (sk_C @ X21 @ X22))
% 0.21/0.58          | (v2_tex_2 @ X21 @ X22)
% 0.21/0.58          | ~ (l1_pre_topc @ X22))),
% 0.21/0.58      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.21/0.58  thf('30', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (~ (l1_pre_topc @ X0)
% 0.21/0.58          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.21/0.58          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 0.21/0.58              != (sk_C @ k1_xboole_0 @ X0))
% 0.21/0.58          | ~ (v4_pre_topc @ X1 @ X0)
% 0.21/0.58          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.58  thf('31', plain,
% 0.21/0.58      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 0.21/0.58      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.58  thf(commutativity_k9_subset_1, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.58       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.21/0.58  thf('32', plain,
% 0.21/0.58      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.58         (((k9_subset_1 @ X6 @ X8 @ X7) = (k9_subset_1 @ X6 @ X7 @ X8))
% 0.21/0.58          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.21/0.58      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.21/0.58  thf('33', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.21/0.58           = (k9_subset_1 @ X0 @ k1_xboole_0 @ X1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.58  thf('34', plain,
% 0.21/0.58      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 0.21/0.58      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.58  thf(redefinition_k9_subset_1, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.58       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.21/0.58  thf('35', plain,
% 0.21/0.58      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.58         (((k9_subset_1 @ X13 @ X11 @ X12) = (k3_xboole_0 @ X11 @ X12))
% 0.21/0.58          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.21/0.58      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.21/0.58  thf('36', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.21/0.58           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.58  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.58    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.58  thf('37', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.58  thf(t17_xboole_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.58  thf('38', plain,
% 0.21/0.58      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 0.21/0.58      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.21/0.58  thf('39', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.21/0.58      inference('sup+', [status(thm)], ['37', '38'])).
% 0.21/0.58  thf('40', plain,
% 0.21/0.58      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ k1_xboole_0))),
% 0.21/0.58      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.21/0.58  thf('41', plain,
% 0.21/0.58      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.58  thf('42', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.58      inference('demod', [status(thm)], ['36', '41'])).
% 0.21/0.58  thf('43', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         ((k1_xboole_0) = (k9_subset_1 @ X0 @ k1_xboole_0 @ X1))),
% 0.21/0.58      inference('demod', [status(thm)], ['33', '42'])).
% 0.21/0.58  thf('44', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (~ (l1_pre_topc @ X0)
% 0.21/0.58          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.21/0.58          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.21/0.58          | ~ (v4_pre_topc @ X1 @ X0)
% 0.21/0.58          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.58      inference('demod', [status(thm)], ['30', '43'])).
% 0.21/0.58  thf('45', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.21/0.58          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.21/0.58          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.21/0.58          | ~ (l1_pre_topc @ X0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['27', '44'])).
% 0.21/0.58  thf('46', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v4_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 0.21/0.58          | ~ (l1_struct_0 @ X0)
% 0.21/0.58          | ~ (l1_pre_topc @ X0)
% 0.21/0.58          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.21/0.58          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['24', '45'])).
% 0.21/0.58  thf('47', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v2_pre_topc @ X0)
% 0.21/0.58          | ~ (l1_pre_topc @ X0)
% 0.21/0.58          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.21/0.58          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.21/0.58          | ~ (l1_pre_topc @ X0)
% 0.21/0.58          | ~ (l1_struct_0 @ X0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['23', '46'])).
% 0.21/0.58  thf('48', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (l1_struct_0 @ X0)
% 0.21/0.58          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.21/0.58          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.21/0.58          | ~ (l1_pre_topc @ X0)
% 0.21/0.58          | ~ (v2_pre_topc @ X0))),
% 0.21/0.58      inference('simplify', [status(thm)], ['47'])).
% 0.21/0.58  thf('49', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (((k1_xboole_0) != (sk_C @ X0 @ X1))
% 0.21/0.58          | ~ (v1_xboole_0 @ X0)
% 0.21/0.58          | ~ (v2_pre_topc @ X1)
% 0.21/0.58          | ~ (l1_pre_topc @ X1)
% 0.21/0.58          | (v2_tex_2 @ k1_xboole_0 @ X1)
% 0.21/0.58          | ~ (l1_struct_0 @ X1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['22', '48'])).
% 0.21/0.58  thf('50', plain,
% 0.21/0.58      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.58        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.58        | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 0.21/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.58        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['21', '49'])).
% 0.21/0.58  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(dt_l1_pre_topc, axiom,
% 0.21/0.58    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.58  thf('52', plain,
% 0.21/0.58      (![X19 : $i]: ((l1_struct_0 @ X19) | ~ (l1_pre_topc @ X19))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.58  thf('53', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.58      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.58  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('55', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('56', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.58      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.58  thf('57', plain,
% 0.21/0.58      ((((k1_xboole_0) != (k1_xboole_0)) | (v2_tex_2 @ k1_xboole_0 @ sk_A))),
% 0.21/0.58      inference('demod', [status(thm)], ['50', '53', '54', '55', '56'])).
% 0.21/0.58  thf('58', plain, ((v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.21/0.58      inference('simplify', [status(thm)], ['57'])).
% 0.21/0.58  thf('59', plain, ($false), inference('demod', [status(thm)], ['4', '58'])).
% 0.21/0.58  
% 0.21/0.58  % SZS output end Refutation
% 0.21/0.58  
% 0.21/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
