%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RJHDEJFbrO

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:37 EST 2020

% Result     : Theorem 0.84s
% Output     : Refutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 133 expanded)
%              Number of leaves         :   31 (  54 expanded)
%              Depth                    :   19
%              Number of atoms          :  589 (1031 expanded)
%              Number of equality atoms :   33 (  42 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

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
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('3',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
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

thf('6',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( r1_tarski @ ( sk_C_1 @ X23 @ X24 ) @ X23 )
      | ( v2_tex_2 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('11',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( ( sk_C_1 @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('17',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_C_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['13','14','17'])).

thf(rc2_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ( v3_pre_topc @ B @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X22: $i] :
      ( ( v3_pre_topc @ ( sk_B @ X22 ) @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[rc2_tops_1])).

thf('20',plain,(
    ! [X22: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[rc2_tops_1])).

thf('21',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('22',plain,(
    ! [X23: $i,X24: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v3_pre_topc @ X26 @ X24 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X24 ) @ X23 @ X26 )
       != ( sk_C_1 @ X23 @ X24 ) )
      | ( v2_tex_2 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ X1 )
       != ( sk_C_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('25',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k9_subset_1 @ X6 @ X8 @ X7 )
        = ( k9_subset_1 @ X6 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k9_subset_1 @ X0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('28',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k9_subset_1 @ X14 @ X12 @ X13 )
        = ( k3_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('30',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('31',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('34',plain,(
    ! [X16: $i,X18: $i] :
      ( ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('36',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X9 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('43',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k9_subset_1 @ X14 @ X12 @ X13 )
        = ( k3_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k9_subset_1 @ X0 @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['26','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['23','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_pre_topc @ ( sk_B @ X0 ) @ X0 )
      | ( k1_xboole_0
       != ( sk_C_1 @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v3_pre_topc @ ( sk_B @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( k1_xboole_0
       != ( sk_C_1 @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','52'])).

thf('54',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    v2_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['4','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RJHDEJFbrO
% 0.14/0.33  % Computer   : n003.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 10:58:57 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  % Running portfolio for 600 s
% 0.14/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.33  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.84/1.07  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.84/1.07  % Solved by: fo/fo7.sh
% 0.84/1.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.84/1.07  % done 924 iterations in 0.623s
% 0.84/1.07  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.84/1.07  % SZS output start Refutation
% 0.84/1.07  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.84/1.07  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.84/1.07  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.84/1.07  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.84/1.07  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.84/1.07  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.84/1.07  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.84/1.07  thf(sk_B_type, type, sk_B: $i > $i).
% 0.84/1.07  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.84/1.07  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.84/1.07  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.84/1.07  thf(sk_A_type, type, sk_A: $i).
% 0.84/1.07  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.84/1.07  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.84/1.07  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.84/1.07  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.84/1.07  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.84/1.07  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.84/1.07  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.84/1.07  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.84/1.07  thf(t35_tex_2, conjecture,
% 0.84/1.07    (![A:$i]:
% 0.84/1.07     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.84/1.07       ( ![B:$i]:
% 0.84/1.07         ( ( ( v1_xboole_0 @ B ) & 
% 0.84/1.07             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.84/1.07           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.84/1.07  thf(zf_stmt_0, negated_conjecture,
% 0.84/1.07    (~( ![A:$i]:
% 0.84/1.07        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.84/1.07            ( l1_pre_topc @ A ) ) =>
% 0.84/1.07          ( ![B:$i]:
% 0.84/1.07            ( ( ( v1_xboole_0 @ B ) & 
% 0.84/1.07                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.84/1.07              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.84/1.07    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 0.84/1.07  thf('0', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('1', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf(l13_xboole_0, axiom,
% 0.84/1.07    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.84/1.07  thf('2', plain,
% 0.84/1.07      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.84/1.07      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.84/1.07  thf('3', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.84/1.07      inference('sup-', [status(thm)], ['1', '2'])).
% 0.84/1.07  thf('4', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.84/1.07      inference('demod', [status(thm)], ['0', '3'])).
% 0.84/1.07  thf(t4_subset_1, axiom,
% 0.84/1.07    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.84/1.07  thf('5', plain,
% 0.84/1.07      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.84/1.07      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.84/1.07  thf(d5_tex_2, axiom,
% 0.84/1.07    (![A:$i]:
% 0.84/1.07     ( ( l1_pre_topc @ A ) =>
% 0.84/1.07       ( ![B:$i]:
% 0.84/1.07         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.84/1.07           ( ( v2_tex_2 @ B @ A ) <=>
% 0.84/1.07             ( ![C:$i]:
% 0.84/1.07               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.84/1.07                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.84/1.07                      ( ![D:$i]:
% 0.84/1.07                        ( ( m1_subset_1 @
% 0.84/1.07                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.84/1.07                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.84/1.07                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.84/1.07                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.84/1.07  thf('6', plain,
% 0.84/1.07      (![X23 : $i, X24 : $i]:
% 0.84/1.07         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.84/1.07          | (r1_tarski @ (sk_C_1 @ X23 @ X24) @ X23)
% 0.84/1.07          | (v2_tex_2 @ X23 @ X24)
% 0.84/1.07          | ~ (l1_pre_topc @ X24))),
% 0.84/1.07      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.84/1.07  thf('7', plain,
% 0.84/1.07      (![X0 : $i]:
% 0.84/1.07         (~ (l1_pre_topc @ X0)
% 0.84/1.07          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.84/1.07          | (r1_tarski @ (sk_C_1 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.84/1.07      inference('sup-', [status(thm)], ['5', '6'])).
% 0.84/1.07  thf(t3_xboole_1, axiom,
% 0.84/1.07    (![A:$i]:
% 0.84/1.07     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.84/1.07  thf('8', plain,
% 0.84/1.07      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ k1_xboole_0))),
% 0.84/1.07      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.84/1.07  thf('9', plain,
% 0.84/1.07      (![X0 : $i]:
% 0.84/1.07         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.84/1.07          | ~ (l1_pre_topc @ X0)
% 0.84/1.07          | ((sk_C_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.84/1.07      inference('sup-', [status(thm)], ['7', '8'])).
% 0.84/1.07  thf('10', plain,
% 0.84/1.07      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.84/1.07      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.84/1.07  thf('11', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.84/1.07      inference('demod', [status(thm)], ['0', '3'])).
% 0.84/1.07  thf('12', plain,
% 0.84/1.07      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.84/1.07      inference('sup-', [status(thm)], ['10', '11'])).
% 0.84/1.07  thf('13', plain,
% 0.84/1.07      ((((sk_C_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))
% 0.84/1.07        | ~ (l1_pre_topc @ sk_A)
% 0.84/1.07        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.84/1.07      inference('sup-', [status(thm)], ['9', '12'])).
% 0.84/1.07  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('15', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('16', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.84/1.07      inference('sup-', [status(thm)], ['1', '2'])).
% 0.84/1.07  thf('17', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.84/1.07      inference('demod', [status(thm)], ['15', '16'])).
% 0.84/1.07  thf('18', plain, (((sk_C_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.84/1.07      inference('demod', [status(thm)], ['13', '14', '17'])).
% 0.84/1.07  thf(rc2_tops_1, axiom,
% 0.84/1.07    (![A:$i]:
% 0.84/1.07     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.84/1.07       ( ?[B:$i]:
% 0.84/1.07         ( ( v4_pre_topc @ B @ A ) & ( v3_pre_topc @ B @ A ) & 
% 0.84/1.07           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.84/1.07  thf('19', plain,
% 0.84/1.07      (![X22 : $i]:
% 0.84/1.07         ((v3_pre_topc @ (sk_B @ X22) @ X22)
% 0.84/1.07          | ~ (l1_pre_topc @ X22)
% 0.84/1.07          | ~ (v2_pre_topc @ X22))),
% 0.84/1.07      inference('cnf', [status(esa)], [rc2_tops_1])).
% 0.84/1.07  thf('20', plain,
% 0.84/1.07      (![X22 : $i]:
% 0.84/1.07         ((m1_subset_1 @ (sk_B @ X22) @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.84/1.07          | ~ (l1_pre_topc @ X22)
% 0.84/1.07          | ~ (v2_pre_topc @ X22))),
% 0.84/1.07      inference('cnf', [status(esa)], [rc2_tops_1])).
% 0.84/1.07  thf('21', plain,
% 0.84/1.07      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.84/1.07      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.84/1.07  thf('22', plain,
% 0.84/1.07      (![X23 : $i, X24 : $i, X26 : $i]:
% 0.84/1.07         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.84/1.07          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.84/1.07          | ~ (v3_pre_topc @ X26 @ X24)
% 0.84/1.07          | ((k9_subset_1 @ (u1_struct_0 @ X24) @ X23 @ X26)
% 0.84/1.07              != (sk_C_1 @ X23 @ X24))
% 0.84/1.07          | (v2_tex_2 @ X23 @ X24)
% 0.84/1.07          | ~ (l1_pre_topc @ X24))),
% 0.84/1.07      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.84/1.07  thf('23', plain,
% 0.84/1.07      (![X0 : $i, X1 : $i]:
% 0.84/1.07         (~ (l1_pre_topc @ X0)
% 0.84/1.07          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.84/1.07          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 0.84/1.07              != (sk_C_1 @ k1_xboole_0 @ X0))
% 0.84/1.07          | ~ (v3_pre_topc @ X1 @ X0)
% 0.84/1.07          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.84/1.07      inference('sup-', [status(thm)], ['21', '22'])).
% 0.84/1.07  thf('24', plain,
% 0.84/1.07      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.84/1.07      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.84/1.07  thf(commutativity_k9_subset_1, axiom,
% 0.84/1.07    (![A:$i,B:$i,C:$i]:
% 0.84/1.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.84/1.07       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.84/1.07  thf('25', plain,
% 0.84/1.07      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.84/1.07         (((k9_subset_1 @ X6 @ X8 @ X7) = (k9_subset_1 @ X6 @ X7 @ X8))
% 0.84/1.07          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.84/1.07      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.84/1.07  thf('26', plain,
% 0.84/1.07      (![X0 : $i, X1 : $i]:
% 0.84/1.07         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.84/1.07           = (k9_subset_1 @ X0 @ k1_xboole_0 @ X1))),
% 0.84/1.07      inference('sup-', [status(thm)], ['24', '25'])).
% 0.84/1.07  thf('27', plain,
% 0.84/1.07      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.84/1.07      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.84/1.07  thf(redefinition_k9_subset_1, axiom,
% 0.84/1.07    (![A:$i,B:$i,C:$i]:
% 0.84/1.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.84/1.07       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.84/1.07  thf('28', plain,
% 0.84/1.07      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.84/1.07         (((k9_subset_1 @ X14 @ X12 @ X13) = (k3_xboole_0 @ X12 @ X13))
% 0.84/1.07          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.84/1.07      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.84/1.07  thf('29', plain,
% 0.84/1.07      (![X0 : $i, X1 : $i]:
% 0.84/1.07         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.84/1.07           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 0.84/1.07      inference('sup-', [status(thm)], ['27', '28'])).
% 0.84/1.07  thf(d3_tarski, axiom,
% 0.84/1.07    (![A:$i,B:$i]:
% 0.84/1.07     ( ( r1_tarski @ A @ B ) <=>
% 0.84/1.07       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.84/1.07  thf('30', plain,
% 0.84/1.07      (![X1 : $i, X3 : $i]:
% 0.84/1.07         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.84/1.07      inference('cnf', [status(esa)], [d3_tarski])).
% 0.84/1.07  thf('31', plain,
% 0.84/1.07      (![X1 : $i, X3 : $i]:
% 0.84/1.07         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.84/1.07      inference('cnf', [status(esa)], [d3_tarski])).
% 0.84/1.07  thf('32', plain,
% 0.84/1.07      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.84/1.07      inference('sup-', [status(thm)], ['30', '31'])).
% 0.84/1.07  thf('33', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.84/1.07      inference('simplify', [status(thm)], ['32'])).
% 0.84/1.07  thf(t3_subset, axiom,
% 0.84/1.07    (![A:$i,B:$i]:
% 0.84/1.07     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.84/1.07  thf('34', plain,
% 0.84/1.07      (![X16 : $i, X18 : $i]:
% 0.84/1.07         ((m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X16 @ X18))),
% 0.84/1.07      inference('cnf', [status(esa)], [t3_subset])).
% 0.84/1.07  thf('35', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.84/1.07      inference('sup-', [status(thm)], ['33', '34'])).
% 0.84/1.07  thf(dt_k9_subset_1, axiom,
% 0.84/1.07    (![A:$i,B:$i,C:$i]:
% 0.84/1.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.84/1.07       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.84/1.07  thf('36', plain,
% 0.84/1.07      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.84/1.07         ((m1_subset_1 @ (k9_subset_1 @ X9 @ X10 @ X11) @ (k1_zfmisc_1 @ X9))
% 0.84/1.07          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X9)))),
% 0.84/1.07      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.84/1.07  thf('37', plain,
% 0.84/1.07      (![X0 : $i, X1 : $i]:
% 0.84/1.07         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.84/1.07      inference('sup-', [status(thm)], ['35', '36'])).
% 0.84/1.07  thf('38', plain,
% 0.84/1.07      (![X16 : $i, X17 : $i]:
% 0.84/1.07         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.84/1.07      inference('cnf', [status(esa)], [t3_subset])).
% 0.84/1.07  thf('39', plain,
% 0.84/1.07      (![X0 : $i, X1 : $i]: (r1_tarski @ (k9_subset_1 @ X0 @ X1 @ X0) @ X0)),
% 0.84/1.07      inference('sup-', [status(thm)], ['37', '38'])).
% 0.84/1.07  thf('40', plain,
% 0.84/1.07      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ k1_xboole_0))),
% 0.84/1.07      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.84/1.07  thf('41', plain,
% 0.84/1.07      (![X0 : $i]:
% 0.84/1.07         ((k9_subset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.84/1.07      inference('sup-', [status(thm)], ['39', '40'])).
% 0.84/1.07  thf('42', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.84/1.07      inference('sup-', [status(thm)], ['33', '34'])).
% 0.84/1.07  thf('43', plain,
% 0.84/1.07      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.84/1.07         (((k9_subset_1 @ X14 @ X12 @ X13) = (k3_xboole_0 @ X12 @ X13))
% 0.84/1.07          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.84/1.07      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.84/1.07  thf('44', plain,
% 0.84/1.07      (![X0 : $i, X1 : $i]:
% 0.84/1.07         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.84/1.07      inference('sup-', [status(thm)], ['42', '43'])).
% 0.84/1.07  thf('45', plain,
% 0.84/1.07      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.84/1.07      inference('demod', [status(thm)], ['41', '44'])).
% 0.84/1.07  thf('46', plain,
% 0.84/1.07      (![X0 : $i, X1 : $i]:
% 0.84/1.07         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.84/1.07      inference('demod', [status(thm)], ['29', '45'])).
% 0.84/1.07  thf('47', plain,
% 0.84/1.07      (![X0 : $i, X1 : $i]:
% 0.84/1.07         ((k1_xboole_0) = (k9_subset_1 @ X0 @ k1_xboole_0 @ X1))),
% 0.84/1.07      inference('demod', [status(thm)], ['26', '46'])).
% 0.84/1.07  thf('48', plain,
% 0.84/1.07      (![X0 : $i, X1 : $i]:
% 0.84/1.07         (~ (l1_pre_topc @ X0)
% 0.84/1.07          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.84/1.07          | ((k1_xboole_0) != (sk_C_1 @ k1_xboole_0 @ X0))
% 0.84/1.07          | ~ (v3_pre_topc @ X1 @ X0)
% 0.84/1.07          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.84/1.07      inference('demod', [status(thm)], ['23', '47'])).
% 0.84/1.07  thf('49', plain,
% 0.84/1.07      (![X0 : $i]:
% 0.84/1.07         (~ (v2_pre_topc @ X0)
% 0.84/1.07          | ~ (l1_pre_topc @ X0)
% 0.84/1.07          | ~ (v3_pre_topc @ (sk_B @ X0) @ X0)
% 0.84/1.07          | ((k1_xboole_0) != (sk_C_1 @ k1_xboole_0 @ X0))
% 0.84/1.07          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.84/1.07          | ~ (l1_pre_topc @ X0))),
% 0.84/1.07      inference('sup-', [status(thm)], ['20', '48'])).
% 0.84/1.07  thf('50', plain,
% 0.84/1.07      (![X0 : $i]:
% 0.84/1.07         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.84/1.07          | ((k1_xboole_0) != (sk_C_1 @ k1_xboole_0 @ X0))
% 0.84/1.07          | ~ (v3_pre_topc @ (sk_B @ X0) @ X0)
% 0.84/1.07          | ~ (l1_pre_topc @ X0)
% 0.84/1.07          | ~ (v2_pre_topc @ X0))),
% 0.84/1.07      inference('simplify', [status(thm)], ['49'])).
% 0.84/1.07  thf('51', plain,
% 0.84/1.07      (![X0 : $i]:
% 0.84/1.07         (~ (v2_pre_topc @ X0)
% 0.84/1.07          | ~ (l1_pre_topc @ X0)
% 0.84/1.07          | ~ (v2_pre_topc @ X0)
% 0.84/1.07          | ~ (l1_pre_topc @ X0)
% 0.84/1.07          | ((k1_xboole_0) != (sk_C_1 @ k1_xboole_0 @ X0))
% 0.84/1.07          | (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.84/1.07      inference('sup-', [status(thm)], ['19', '50'])).
% 0.84/1.07  thf('52', plain,
% 0.84/1.07      (![X0 : $i]:
% 0.84/1.07         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.84/1.07          | ((k1_xboole_0) != (sk_C_1 @ k1_xboole_0 @ X0))
% 0.84/1.07          | ~ (l1_pre_topc @ X0)
% 0.84/1.07          | ~ (v2_pre_topc @ X0))),
% 0.84/1.07      inference('simplify', [status(thm)], ['51'])).
% 0.84/1.07  thf('53', plain,
% 0.84/1.07      ((((k1_xboole_0) != (k1_xboole_0))
% 0.84/1.07        | ~ (v2_pre_topc @ sk_A)
% 0.84/1.07        | ~ (l1_pre_topc @ sk_A)
% 0.84/1.07        | (v2_tex_2 @ k1_xboole_0 @ sk_A))),
% 0.84/1.07      inference('sup-', [status(thm)], ['18', '52'])).
% 0.84/1.07  thf('54', plain, ((v2_pre_topc @ sk_A)),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('56', plain,
% 0.84/1.07      ((((k1_xboole_0) != (k1_xboole_0)) | (v2_tex_2 @ k1_xboole_0 @ sk_A))),
% 0.84/1.07      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.84/1.07  thf('57', plain, ((v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.84/1.07      inference('simplify', [status(thm)], ['56'])).
% 0.84/1.07  thf('58', plain, ($false), inference('demod', [status(thm)], ['4', '57'])).
% 0.84/1.07  
% 0.84/1.07  % SZS output end Refutation
% 0.84/1.07  
% 0.84/1.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
