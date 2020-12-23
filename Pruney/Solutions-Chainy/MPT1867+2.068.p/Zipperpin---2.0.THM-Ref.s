%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.57vRKy6nZf

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:35 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 141 expanded)
%              Number of leaves         :   36 (  58 expanded)
%              Depth                    :   16
%              Number of atoms          :  589 (1057 expanded)
%              Number of equality atoms :   44 (  57 expanded)
%              Maximal formula depth    :   19 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

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

thf('6',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( r1_tarski @ ( sk_C @ X23 @ X24 ) @ X23 )
      | ( v2_tex_2 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
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
    ( ( ( sk_C @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_xboole_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('17',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['13','14','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(fc4_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('20',plain,(
    ! [X22: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X22 ) @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc4_pre_topc])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('21',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('22',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X10 ) @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('23',plain,(
    ! [X9: $i] :
      ( ( k2_subset_1 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('24',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('26',plain,(
    ! [X23: $i,X24: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v4_pre_topc @ X26 @ X24 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X24 ) @ X23 @ X26 )
       != ( sk_C @ X23 @ X24 ) )
      | ( v2_tex_2 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ X1 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v4_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('29',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k9_subset_1 @ X6 @ X8 @ X7 )
        = ( k9_subset_1 @ X6 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k9_subset_1 @ X0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('32',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k9_subset_1 @ X13 @ X11 @ X12 )
        = ( k3_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('34',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_tarski @ X5 @ X4 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('35',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('39',plain,(
    ! [X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X2 ) @ X1 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('40',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k9_subset_1 @ X0 @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['30','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v4_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['27','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
       != ( sk_C @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_tex_2 @ k1_xboole_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','49'])).

thf('51',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('53',plain,(
    ! [X21: $i] :
      ( ( l1_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('54',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['15','16'])).

thf('58',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['51','54','55','56','57'])).

thf('59',plain,(
    v2_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['4','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.57vRKy6nZf
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:40:53 EST 2020
% 0.21/0.34  % CPUTime    : 
% 0.21/0.34  % Running portfolio for 600 s
% 0.21/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.21/0.34  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.77/0.94  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.77/0.94  % Solved by: fo/fo7.sh
% 0.77/0.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/0.94  % done 696 iterations in 0.451s
% 0.77/0.94  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.77/0.94  % SZS output start Refutation
% 0.77/0.94  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.77/0.94  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.77/0.94  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.77/0.94  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.77/0.94  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.77/0.94  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.77/0.94  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.77/0.94  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.77/0.94  thf(sk_A_type, type, sk_A: $i).
% 0.77/0.94  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.77/0.94  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.77/0.94  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.77/0.94  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.77/0.94  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.77/0.94  thf(sk_B_type, type, sk_B: $i).
% 0.77/0.94  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.77/0.94  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.77/0.94  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.77/0.94  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.77/0.94  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.77/0.94  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.77/0.94  thf(t35_tex_2, conjecture,
% 0.77/0.94    (![A:$i]:
% 0.77/0.94     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.77/0.94       ( ![B:$i]:
% 0.77/0.94         ( ( ( v1_xboole_0 @ B ) & 
% 0.77/0.94             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.77/0.94           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.77/0.94  thf(zf_stmt_0, negated_conjecture,
% 0.77/0.94    (~( ![A:$i]:
% 0.77/0.94        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.77/0.94            ( l1_pre_topc @ A ) ) =>
% 0.77/0.94          ( ![B:$i]:
% 0.77/0.94            ( ( ( v1_xboole_0 @ B ) & 
% 0.77/0.94                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.77/0.94              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.77/0.94    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 0.77/0.94  thf('0', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('1', plain, ((v1_xboole_0 @ sk_B)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf(l13_xboole_0, axiom,
% 0.77/0.94    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.77/0.94  thf('2', plain,
% 0.77/0.94      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.77/0.94      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.77/0.94  thf('3', plain, (((sk_B) = (k1_xboole_0))),
% 0.77/0.94      inference('sup-', [status(thm)], ['1', '2'])).
% 0.77/0.94  thf('4', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.77/0.94      inference('demod', [status(thm)], ['0', '3'])).
% 0.77/0.94  thf(t4_subset_1, axiom,
% 0.77/0.94    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.77/0.94  thf('5', plain,
% 0.77/0.94      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 0.77/0.94      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.77/0.94  thf(d6_tex_2, axiom,
% 0.77/0.94    (![A:$i]:
% 0.77/0.94     ( ( l1_pre_topc @ A ) =>
% 0.77/0.94       ( ![B:$i]:
% 0.77/0.94         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.94           ( ( v2_tex_2 @ B @ A ) <=>
% 0.77/0.94             ( ![C:$i]:
% 0.77/0.94               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.94                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.77/0.94                      ( ![D:$i]:
% 0.77/0.94                        ( ( m1_subset_1 @
% 0.77/0.94                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.94                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.77/0.94                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.77/0.94                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.77/0.94  thf('6', plain,
% 0.77/0.94      (![X23 : $i, X24 : $i]:
% 0.77/0.94         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.77/0.94          | (r1_tarski @ (sk_C @ X23 @ X24) @ X23)
% 0.77/0.94          | (v2_tex_2 @ X23 @ X24)
% 0.77/0.94          | ~ (l1_pre_topc @ X24))),
% 0.77/0.94      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.77/0.94  thf('7', plain,
% 0.77/0.94      (![X0 : $i]:
% 0.77/0.94         (~ (l1_pre_topc @ X0)
% 0.77/0.94          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.77/0.94          | (r1_tarski @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.77/0.94      inference('sup-', [status(thm)], ['5', '6'])).
% 0.77/0.94  thf(t3_xboole_1, axiom,
% 0.77/0.94    (![A:$i]:
% 0.77/0.94     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.77/0.94  thf('8', plain,
% 0.77/0.94      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 0.77/0.94      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.77/0.94  thf('9', plain,
% 0.77/0.94      (![X0 : $i]:
% 0.77/0.94         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.77/0.94          | ~ (l1_pre_topc @ X0)
% 0.77/0.94          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.77/0.94      inference('sup-', [status(thm)], ['7', '8'])).
% 0.77/0.94  thf('10', plain,
% 0.77/0.94      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.77/0.94      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.77/0.94  thf('11', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.77/0.94      inference('demod', [status(thm)], ['0', '3'])).
% 0.77/0.94  thf('12', plain,
% 0.77/0.94      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.77/0.94      inference('sup-', [status(thm)], ['10', '11'])).
% 0.77/0.94  thf('13', plain,
% 0.77/0.94      ((((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))
% 0.77/0.94        | ~ (l1_pre_topc @ sk_A)
% 0.77/0.94        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.77/0.94      inference('sup-', [status(thm)], ['9', '12'])).
% 0.77/0.94  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('15', plain, ((v1_xboole_0 @ sk_B)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('16', plain, (((sk_B) = (k1_xboole_0))),
% 0.77/0.94      inference('sup-', [status(thm)], ['1', '2'])).
% 0.77/0.94  thf('17', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.77/0.94      inference('demod', [status(thm)], ['15', '16'])).
% 0.77/0.94  thf('18', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.77/0.94      inference('demod', [status(thm)], ['13', '14', '17'])).
% 0.77/0.94  thf('19', plain,
% 0.77/0.94      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.77/0.94      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.77/0.94  thf(fc4_pre_topc, axiom,
% 0.77/0.94    (![A:$i]:
% 0.77/0.94     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.77/0.94       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.77/0.94  thf('20', plain,
% 0.77/0.94      (![X22 : $i]:
% 0.77/0.94         ((v4_pre_topc @ (k2_struct_0 @ X22) @ X22)
% 0.77/0.94          | ~ (l1_pre_topc @ X22)
% 0.77/0.94          | ~ (v2_pre_topc @ X22))),
% 0.77/0.94      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.77/0.94  thf(d3_struct_0, axiom,
% 0.77/0.94    (![A:$i]:
% 0.77/0.94     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.77/0.94  thf('21', plain,
% 0.77/0.94      (![X20 : $i]:
% 0.77/0.94         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.77/0.94      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.77/0.94  thf(dt_k2_subset_1, axiom,
% 0.77/0.94    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.77/0.94  thf('22', plain,
% 0.77/0.94      (![X10 : $i]: (m1_subset_1 @ (k2_subset_1 @ X10) @ (k1_zfmisc_1 @ X10))),
% 0.77/0.94      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.77/0.94  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.77/0.94  thf('23', plain, (![X9 : $i]: ((k2_subset_1 @ X9) = (X9))),
% 0.77/0.94      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.77/0.94  thf('24', plain, (![X10 : $i]: (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X10))),
% 0.77/0.94      inference('demod', [status(thm)], ['22', '23'])).
% 0.77/0.94  thf('25', plain,
% 0.77/0.94      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 0.77/0.94      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.77/0.94  thf('26', plain,
% 0.77/0.94      (![X23 : $i, X24 : $i, X26 : $i]:
% 0.77/0.94         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.77/0.94          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.77/0.94          | ~ (v4_pre_topc @ X26 @ X24)
% 0.77/0.94          | ((k9_subset_1 @ (u1_struct_0 @ X24) @ X23 @ X26)
% 0.77/0.94              != (sk_C @ X23 @ X24))
% 0.77/0.94          | (v2_tex_2 @ X23 @ X24)
% 0.77/0.94          | ~ (l1_pre_topc @ X24))),
% 0.77/0.94      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.77/0.94  thf('27', plain,
% 0.77/0.94      (![X0 : $i, X1 : $i]:
% 0.77/0.94         (~ (l1_pre_topc @ X0)
% 0.77/0.94          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.77/0.94          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 0.77/0.94              != (sk_C @ k1_xboole_0 @ X0))
% 0.77/0.94          | ~ (v4_pre_topc @ X1 @ X0)
% 0.77/0.94          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['25', '26'])).
% 0.77/0.94  thf('28', plain,
% 0.77/0.94      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 0.77/0.94      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.77/0.94  thf(commutativity_k9_subset_1, axiom,
% 0.77/0.94    (![A:$i,B:$i,C:$i]:
% 0.77/0.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.77/0.94       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.77/0.94  thf('29', plain,
% 0.77/0.94      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.77/0.94         (((k9_subset_1 @ X6 @ X8 @ X7) = (k9_subset_1 @ X6 @ X7 @ X8))
% 0.77/0.94          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.77/0.94      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.77/0.94  thf('30', plain,
% 0.77/0.94      (![X0 : $i, X1 : $i]:
% 0.77/0.94         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.77/0.94           = (k9_subset_1 @ X0 @ k1_xboole_0 @ X1))),
% 0.77/0.94      inference('sup-', [status(thm)], ['28', '29'])).
% 0.77/0.94  thf('31', plain,
% 0.77/0.94      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 0.77/0.94      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.77/0.94  thf(redefinition_k9_subset_1, axiom,
% 0.77/0.94    (![A:$i,B:$i,C:$i]:
% 0.77/0.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.77/0.94       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.77/0.94  thf('32', plain,
% 0.77/0.94      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.77/0.94         (((k9_subset_1 @ X13 @ X11 @ X12) = (k3_xboole_0 @ X11 @ X12))
% 0.77/0.94          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.77/0.94      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.77/0.94  thf('33', plain,
% 0.77/0.94      (![X0 : $i, X1 : $i]:
% 0.77/0.94         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.77/0.94           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 0.77/0.94      inference('sup-', [status(thm)], ['31', '32'])).
% 0.77/0.94  thf(commutativity_k2_tarski, axiom,
% 0.77/0.94    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.77/0.94  thf('34', plain,
% 0.77/0.94      (![X4 : $i, X5 : $i]: ((k2_tarski @ X5 @ X4) = (k2_tarski @ X4 @ X5))),
% 0.77/0.94      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.77/0.94  thf(t12_setfam_1, axiom,
% 0.77/0.94    (![A:$i,B:$i]:
% 0.77/0.94     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.77/0.94  thf('35', plain,
% 0.77/0.94      (![X15 : $i, X16 : $i]:
% 0.77/0.94         ((k1_setfam_1 @ (k2_tarski @ X15 @ X16)) = (k3_xboole_0 @ X15 @ X16))),
% 0.77/0.94      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.77/0.94  thf('36', plain,
% 0.77/0.94      (![X0 : $i, X1 : $i]:
% 0.77/0.94         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.77/0.94      inference('sup+', [status(thm)], ['34', '35'])).
% 0.77/0.94  thf('37', plain,
% 0.77/0.94      (![X15 : $i, X16 : $i]:
% 0.77/0.94         ((k1_setfam_1 @ (k2_tarski @ X15 @ X16)) = (k3_xboole_0 @ X15 @ X16))),
% 0.77/0.94      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.77/0.94  thf('38', plain,
% 0.77/0.94      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.77/0.94      inference('sup+', [status(thm)], ['36', '37'])).
% 0.77/0.94  thf(t17_xboole_1, axiom,
% 0.77/0.94    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.77/0.94  thf('39', plain,
% 0.77/0.94      (![X1 : $i, X2 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X2) @ X1)),
% 0.77/0.94      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.77/0.94  thf('40', plain,
% 0.77/0.94      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 0.77/0.94      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.77/0.94  thf('41', plain,
% 0.77/0.94      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.77/0.94      inference('sup-', [status(thm)], ['39', '40'])).
% 0.77/0.94  thf('42', plain,
% 0.77/0.94      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.77/0.94      inference('sup+', [status(thm)], ['38', '41'])).
% 0.77/0.94  thf('43', plain,
% 0.77/0.94      (![X0 : $i, X1 : $i]:
% 0.77/0.94         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.77/0.94      inference('demod', [status(thm)], ['33', '42'])).
% 0.77/0.94  thf('44', plain,
% 0.77/0.94      (![X0 : $i, X1 : $i]:
% 0.77/0.94         ((k1_xboole_0) = (k9_subset_1 @ X0 @ k1_xboole_0 @ X1))),
% 0.77/0.94      inference('demod', [status(thm)], ['30', '43'])).
% 0.77/0.94  thf('45', plain,
% 0.77/0.94      (![X0 : $i, X1 : $i]:
% 0.77/0.94         (~ (l1_pre_topc @ X0)
% 0.77/0.94          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.77/0.94          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.77/0.94          | ~ (v4_pre_topc @ X1 @ X0)
% 0.77/0.94          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.77/0.94      inference('demod', [status(thm)], ['27', '44'])).
% 0.77/0.94  thf('46', plain,
% 0.77/0.94      (![X0 : $i]:
% 0.77/0.94         (~ (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.77/0.94          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.77/0.94          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.77/0.94          | ~ (l1_pre_topc @ X0))),
% 0.77/0.94      inference('sup-', [status(thm)], ['24', '45'])).
% 0.77/0.94  thf('47', plain,
% 0.77/0.94      (![X0 : $i]:
% 0.77/0.94         (~ (v4_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 0.77/0.94          | ~ (l1_struct_0 @ X0)
% 0.77/0.94          | ~ (l1_pre_topc @ X0)
% 0.77/0.94          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.77/0.94          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0)))),
% 0.77/0.94      inference('sup-', [status(thm)], ['21', '46'])).
% 0.77/0.94  thf('48', plain,
% 0.77/0.94      (![X0 : $i]:
% 0.77/0.94         (~ (v2_pre_topc @ X0)
% 0.77/0.94          | ~ (l1_pre_topc @ X0)
% 0.77/0.94          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.77/0.94          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.77/0.94          | ~ (l1_pre_topc @ X0)
% 0.77/0.94          | ~ (l1_struct_0 @ X0))),
% 0.77/0.94      inference('sup-', [status(thm)], ['20', '47'])).
% 0.77/0.94  thf('49', plain,
% 0.77/0.94      (![X0 : $i]:
% 0.77/0.94         (~ (l1_struct_0 @ X0)
% 0.77/0.94          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.77/0.94          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.77/0.94          | ~ (l1_pre_topc @ X0)
% 0.77/0.94          | ~ (v2_pre_topc @ X0))),
% 0.77/0.94      inference('simplify', [status(thm)], ['48'])).
% 0.77/0.94  thf('50', plain,
% 0.77/0.94      (![X0 : $i, X1 : $i]:
% 0.77/0.94         (((k1_xboole_0) != (sk_C @ X0 @ X1))
% 0.77/0.94          | ~ (v1_xboole_0 @ X0)
% 0.77/0.94          | ~ (v2_pre_topc @ X1)
% 0.77/0.94          | ~ (l1_pre_topc @ X1)
% 0.77/0.94          | (v2_tex_2 @ k1_xboole_0 @ X1)
% 0.77/0.94          | ~ (l1_struct_0 @ X1))),
% 0.77/0.94      inference('sup-', [status(thm)], ['19', '49'])).
% 0.77/0.94  thf('51', plain,
% 0.77/0.94      ((((k1_xboole_0) != (k1_xboole_0))
% 0.77/0.94        | ~ (l1_struct_0 @ sk_A)
% 0.77/0.94        | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 0.77/0.94        | ~ (l1_pre_topc @ sk_A)
% 0.77/0.94        | ~ (v2_pre_topc @ sk_A)
% 0.77/0.94        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.77/0.94      inference('sup-', [status(thm)], ['18', '50'])).
% 0.77/0.94  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf(dt_l1_pre_topc, axiom,
% 0.77/0.94    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.77/0.94  thf('53', plain,
% 0.77/0.94      (![X21 : $i]: ((l1_struct_0 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.77/0.94      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.77/0.94  thf('54', plain, ((l1_struct_0 @ sk_A)),
% 0.77/0.94      inference('sup-', [status(thm)], ['52', '53'])).
% 0.77/0.94  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('56', plain, ((v2_pre_topc @ sk_A)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('57', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.77/0.94      inference('demod', [status(thm)], ['15', '16'])).
% 0.77/0.94  thf('58', plain,
% 0.77/0.94      ((((k1_xboole_0) != (k1_xboole_0)) | (v2_tex_2 @ k1_xboole_0 @ sk_A))),
% 0.77/0.94      inference('demod', [status(thm)], ['51', '54', '55', '56', '57'])).
% 0.77/0.94  thf('59', plain, ((v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.77/0.94      inference('simplify', [status(thm)], ['58'])).
% 0.77/0.94  thf('60', plain, ($false), inference('demod', [status(thm)], ['4', '59'])).
% 0.77/0.94  
% 0.77/0.94  % SZS output end Refutation
% 0.77/0.94  
% 0.78/0.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
