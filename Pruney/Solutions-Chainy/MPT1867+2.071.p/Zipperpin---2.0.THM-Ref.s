%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EFnishdBE2

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:35 EST 2020

% Result     : Theorem 14.03s
% Output     : Refutation 14.03s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 132 expanded)
%              Number of leaves         :   35 (  54 expanded)
%              Depth                    :   15
%              Number of atoms          :  605 ( 989 expanded)
%              Number of equality atoms :   45 (  55 expanded)
%              Maximal formula depth    :   19 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X17: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
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
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( r1_tarski @ ( sk_C @ X24 @ X25 ) @ X24 )
      | ( v2_tex_2 @ X24 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
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
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ k1_xboole_0 ) ) ),
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
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('16',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( sk_C @ X0 @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( sk_C @ X0 @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(fc4_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('22',plain,(
    ! [X23: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X23 ) @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc4_pre_topc])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('23',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('24',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X13 ) @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('25',plain,(
    ! [X12: $i] :
      ( ( k2_subset_1 @ X12 )
      = X12 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('26',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('28',plain,(
    ! [X24: $i,X25: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v4_pre_topc @ X27 @ X25 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X25 ) @ X24 @ X27 )
       != ( sk_C @ X24 @ X25 ) )
      | ( v2_tex_2 @ X24 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
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
    ! [X17: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('31',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k9_subset_1 @ X9 @ X11 @ X10 )
        = ( k9_subset_1 @ X9 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k9_subset_1 @ X0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('34',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k9_subset_1 @ X16 @ X14 @ X15 )
        = ( k3_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('36',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('37',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('38',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k9_subset_1 @ X0 @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['32','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v4_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['29','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','49'])).

thf('51',plain,(
    v1_xboole_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('57',plain,(
    ! [X22: $i] :
      ( ( l1_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('58',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['50','53','54','55','58'])).

thf('60',plain,(
    v2_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    $false ),
    inference(demod,[status(thm)],['4','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EFnishdBE2
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:12:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 14.03/14.23  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 14.03/14.23  % Solved by: fo/fo7.sh
% 14.03/14.23  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 14.03/14.23  % done 24358 iterations in 13.769s
% 14.03/14.23  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 14.03/14.23  % SZS output start Refutation
% 14.03/14.23  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 14.03/14.23  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 14.03/14.23  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 14.03/14.23  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 14.03/14.23  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 14.03/14.23  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 14.03/14.23  thf(sk_A_type, type, sk_A: $i).
% 14.03/14.23  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 14.03/14.23  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 14.03/14.23  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 14.03/14.23  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 14.03/14.23  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 14.03/14.23  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 14.03/14.23  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 14.03/14.23  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 14.03/14.23  thf(sk_B_type, type, sk_B: $i).
% 14.03/14.23  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 14.03/14.23  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 14.03/14.23  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 14.03/14.23  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 14.03/14.23  thf(t35_tex_2, conjecture,
% 14.03/14.23    (![A:$i]:
% 14.03/14.23     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 14.03/14.23       ( ![B:$i]:
% 14.03/14.23         ( ( ( v1_xboole_0 @ B ) & 
% 14.03/14.23             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 14.03/14.23           ( v2_tex_2 @ B @ A ) ) ) ))).
% 14.03/14.23  thf(zf_stmt_0, negated_conjecture,
% 14.03/14.23    (~( ![A:$i]:
% 14.03/14.23        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 14.03/14.23            ( l1_pre_topc @ A ) ) =>
% 14.03/14.23          ( ![B:$i]:
% 14.03/14.23            ( ( ( v1_xboole_0 @ B ) & 
% 14.03/14.23                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 14.03/14.23              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 14.03/14.23    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 14.03/14.23  thf('0', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 14.03/14.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.23  thf('1', plain, ((v1_xboole_0 @ sk_B)),
% 14.03/14.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.23  thf(l13_xboole_0, axiom,
% 14.03/14.23    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 14.03/14.23  thf('2', plain,
% 14.03/14.23      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 14.03/14.23      inference('cnf', [status(esa)], [l13_xboole_0])).
% 14.03/14.23  thf('3', plain, (((sk_B) = (k1_xboole_0))),
% 14.03/14.23      inference('sup-', [status(thm)], ['1', '2'])).
% 14.03/14.23  thf('4', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 14.03/14.23      inference('demod', [status(thm)], ['0', '3'])).
% 14.03/14.23  thf('5', plain,
% 14.03/14.23      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 14.03/14.23      inference('cnf', [status(esa)], [l13_xboole_0])).
% 14.03/14.23  thf(t4_subset_1, axiom,
% 14.03/14.23    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 14.03/14.23  thf('6', plain,
% 14.03/14.23      (![X17 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 14.03/14.23      inference('cnf', [status(esa)], [t4_subset_1])).
% 14.03/14.23  thf('7', plain,
% 14.03/14.23      (![X0 : $i, X1 : $i]:
% 14.03/14.23         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 14.03/14.23      inference('sup+', [status(thm)], ['5', '6'])).
% 14.03/14.23  thf(d6_tex_2, axiom,
% 14.03/14.23    (![A:$i]:
% 14.03/14.23     ( ( l1_pre_topc @ A ) =>
% 14.03/14.23       ( ![B:$i]:
% 14.03/14.23         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 14.03/14.23           ( ( v2_tex_2 @ B @ A ) <=>
% 14.03/14.23             ( ![C:$i]:
% 14.03/14.23               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 14.03/14.23                 ( ~( ( r1_tarski @ C @ B ) & 
% 14.03/14.23                      ( ![D:$i]:
% 14.03/14.23                        ( ( m1_subset_1 @
% 14.03/14.23                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 14.03/14.23                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 14.03/14.23                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 14.03/14.23                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 14.03/14.23  thf('8', plain,
% 14.03/14.23      (![X24 : $i, X25 : $i]:
% 14.03/14.23         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 14.03/14.23          | (r1_tarski @ (sk_C @ X24 @ X25) @ X24)
% 14.03/14.23          | (v2_tex_2 @ X24 @ X25)
% 14.03/14.23          | ~ (l1_pre_topc @ X25))),
% 14.03/14.23      inference('cnf', [status(esa)], [d6_tex_2])).
% 14.03/14.23  thf('9', plain,
% 14.03/14.23      (![X0 : $i, X1 : $i]:
% 14.03/14.23         (~ (v1_xboole_0 @ X1)
% 14.03/14.23          | ~ (l1_pre_topc @ X0)
% 14.03/14.23          | (v2_tex_2 @ X1 @ X0)
% 14.03/14.23          | (r1_tarski @ (sk_C @ X1 @ X0) @ X1))),
% 14.03/14.23      inference('sup-', [status(thm)], ['7', '8'])).
% 14.03/14.23  thf('10', plain,
% 14.03/14.23      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 14.03/14.23      inference('cnf', [status(esa)], [l13_xboole_0])).
% 14.03/14.23  thf(t3_xboole_1, axiom,
% 14.03/14.23    (![A:$i]:
% 14.03/14.23     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 14.03/14.23  thf('11', plain,
% 14.03/14.23      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ k1_xboole_0))),
% 14.03/14.23      inference('cnf', [status(esa)], [t3_xboole_1])).
% 14.03/14.23  thf('12', plain,
% 14.03/14.23      (![X0 : $i, X1 : $i]:
% 14.03/14.23         (~ (r1_tarski @ X1 @ X0)
% 14.03/14.23          | ~ (v1_xboole_0 @ X0)
% 14.03/14.23          | ((X1) = (k1_xboole_0)))),
% 14.03/14.23      inference('sup-', [status(thm)], ['10', '11'])).
% 14.03/14.23  thf('13', plain,
% 14.03/14.23      (![X0 : $i, X1 : $i]:
% 14.03/14.23         ((v2_tex_2 @ X0 @ X1)
% 14.03/14.23          | ~ (l1_pre_topc @ X1)
% 14.03/14.23          | ~ (v1_xboole_0 @ X0)
% 14.03/14.23          | ((sk_C @ X0 @ X1) = (k1_xboole_0))
% 14.03/14.23          | ~ (v1_xboole_0 @ X0))),
% 14.03/14.23      inference('sup-', [status(thm)], ['9', '12'])).
% 14.03/14.23  thf('14', plain,
% 14.03/14.23      (![X0 : $i, X1 : $i]:
% 14.03/14.23         (((sk_C @ X0 @ X1) = (k1_xboole_0))
% 14.03/14.23          | ~ (v1_xboole_0 @ X0)
% 14.03/14.23          | ~ (l1_pre_topc @ X1)
% 14.03/14.23          | (v2_tex_2 @ X0 @ X1))),
% 14.03/14.23      inference('simplify', [status(thm)], ['13'])).
% 14.03/14.23  thf('15', plain,
% 14.03/14.23      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 14.03/14.23      inference('cnf', [status(esa)], [l13_xboole_0])).
% 14.03/14.23  thf('16', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 14.03/14.23      inference('demod', [status(thm)], ['0', '3'])).
% 14.03/14.23  thf('17', plain,
% 14.03/14.23      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 14.03/14.23      inference('sup-', [status(thm)], ['15', '16'])).
% 14.03/14.23  thf('18', plain,
% 14.03/14.23      (![X0 : $i]:
% 14.03/14.23         (~ (l1_pre_topc @ sk_A)
% 14.03/14.23          | ~ (v1_xboole_0 @ X0)
% 14.03/14.23          | ((sk_C @ X0 @ sk_A) = (k1_xboole_0))
% 14.03/14.23          | ~ (v1_xboole_0 @ X0))),
% 14.03/14.23      inference('sup-', [status(thm)], ['14', '17'])).
% 14.03/14.23  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 14.03/14.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.23  thf('20', plain,
% 14.03/14.23      (![X0 : $i]:
% 14.03/14.23         (~ (v1_xboole_0 @ X0)
% 14.03/14.23          | ((sk_C @ X0 @ sk_A) = (k1_xboole_0))
% 14.03/14.23          | ~ (v1_xboole_0 @ X0))),
% 14.03/14.23      inference('demod', [status(thm)], ['18', '19'])).
% 14.03/14.23  thf('21', plain,
% 14.03/14.23      (![X0 : $i]:
% 14.03/14.23         (((sk_C @ X0 @ sk_A) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 14.03/14.23      inference('simplify', [status(thm)], ['20'])).
% 14.03/14.23  thf(fc4_pre_topc, axiom,
% 14.03/14.23    (![A:$i]:
% 14.03/14.23     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 14.03/14.23       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 14.03/14.23  thf('22', plain,
% 14.03/14.23      (![X23 : $i]:
% 14.03/14.23         ((v4_pre_topc @ (k2_struct_0 @ X23) @ X23)
% 14.03/14.23          | ~ (l1_pre_topc @ X23)
% 14.03/14.23          | ~ (v2_pre_topc @ X23))),
% 14.03/14.23      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 14.03/14.23  thf(d3_struct_0, axiom,
% 14.03/14.23    (![A:$i]:
% 14.03/14.23     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 14.03/14.23  thf('23', plain,
% 14.03/14.23      (![X21 : $i]:
% 14.03/14.23         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 14.03/14.23      inference('cnf', [status(esa)], [d3_struct_0])).
% 14.03/14.23  thf(dt_k2_subset_1, axiom,
% 14.03/14.23    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 14.03/14.23  thf('24', plain,
% 14.03/14.23      (![X13 : $i]: (m1_subset_1 @ (k2_subset_1 @ X13) @ (k1_zfmisc_1 @ X13))),
% 14.03/14.23      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 14.03/14.23  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 14.03/14.23  thf('25', plain, (![X12 : $i]: ((k2_subset_1 @ X12) = (X12))),
% 14.03/14.23      inference('cnf', [status(esa)], [d4_subset_1])).
% 14.03/14.23  thf('26', plain, (![X13 : $i]: (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X13))),
% 14.03/14.23      inference('demod', [status(thm)], ['24', '25'])).
% 14.03/14.23  thf('27', plain,
% 14.03/14.23      (![X17 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 14.03/14.23      inference('cnf', [status(esa)], [t4_subset_1])).
% 14.03/14.23  thf('28', plain,
% 14.03/14.23      (![X24 : $i, X25 : $i, X27 : $i]:
% 14.03/14.23         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 14.03/14.23          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 14.03/14.23          | ~ (v4_pre_topc @ X27 @ X25)
% 14.03/14.23          | ((k9_subset_1 @ (u1_struct_0 @ X25) @ X24 @ X27)
% 14.03/14.23              != (sk_C @ X24 @ X25))
% 14.03/14.23          | (v2_tex_2 @ X24 @ X25)
% 14.03/14.23          | ~ (l1_pre_topc @ X25))),
% 14.03/14.23      inference('cnf', [status(esa)], [d6_tex_2])).
% 14.03/14.23  thf('29', plain,
% 14.03/14.23      (![X0 : $i, X1 : $i]:
% 14.03/14.23         (~ (l1_pre_topc @ X0)
% 14.03/14.23          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 14.03/14.23          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 14.03/14.23              != (sk_C @ k1_xboole_0 @ X0))
% 14.03/14.23          | ~ (v4_pre_topc @ X1 @ X0)
% 14.03/14.23          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 14.03/14.23      inference('sup-', [status(thm)], ['27', '28'])).
% 14.03/14.23  thf('30', plain,
% 14.03/14.23      (![X17 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 14.03/14.23      inference('cnf', [status(esa)], [t4_subset_1])).
% 14.03/14.23  thf(commutativity_k9_subset_1, axiom,
% 14.03/14.23    (![A:$i,B:$i,C:$i]:
% 14.03/14.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 14.03/14.23       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 14.03/14.23  thf('31', plain,
% 14.03/14.23      (![X9 : $i, X10 : $i, X11 : $i]:
% 14.03/14.23         (((k9_subset_1 @ X9 @ X11 @ X10) = (k9_subset_1 @ X9 @ X10 @ X11))
% 14.03/14.23          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 14.03/14.23      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 14.03/14.23  thf('32', plain,
% 14.03/14.23      (![X0 : $i, X1 : $i]:
% 14.03/14.23         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 14.03/14.23           = (k9_subset_1 @ X0 @ k1_xboole_0 @ X1))),
% 14.03/14.23      inference('sup-', [status(thm)], ['30', '31'])).
% 14.03/14.23  thf('33', plain,
% 14.03/14.23      (![X17 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 14.03/14.23      inference('cnf', [status(esa)], [t4_subset_1])).
% 14.03/14.23  thf(redefinition_k9_subset_1, axiom,
% 14.03/14.23    (![A:$i,B:$i,C:$i]:
% 14.03/14.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 14.03/14.23       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 14.03/14.23  thf('34', plain,
% 14.03/14.23      (![X14 : $i, X15 : $i, X16 : $i]:
% 14.03/14.23         (((k9_subset_1 @ X16 @ X14 @ X15) = (k3_xboole_0 @ X14 @ X15))
% 14.03/14.23          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 14.03/14.23      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 14.03/14.23  thf('35', plain,
% 14.03/14.23      (![X0 : $i, X1 : $i]:
% 14.03/14.23         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 14.03/14.23           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 14.03/14.23      inference('sup-', [status(thm)], ['33', '34'])).
% 14.03/14.23  thf(t48_xboole_1, axiom,
% 14.03/14.23    (![A:$i,B:$i]:
% 14.03/14.23     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 14.03/14.23  thf('36', plain,
% 14.03/14.23      (![X7 : $i, X8 : $i]:
% 14.03/14.23         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 14.03/14.23           = (k3_xboole_0 @ X7 @ X8))),
% 14.03/14.23      inference('cnf', [status(esa)], [t48_xboole_1])).
% 14.03/14.23  thf(t36_xboole_1, axiom,
% 14.03/14.23    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 14.03/14.23  thf('37', plain,
% 14.03/14.23      (![X3 : $i, X4 : $i]: (r1_tarski @ (k4_xboole_0 @ X3 @ X4) @ X3)),
% 14.03/14.23      inference('cnf', [status(esa)], [t36_xboole_1])).
% 14.03/14.23  thf('38', plain,
% 14.03/14.23      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ k1_xboole_0))),
% 14.03/14.23      inference('cnf', [status(esa)], [t3_xboole_1])).
% 14.03/14.23  thf('39', plain,
% 14.03/14.23      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 14.03/14.23      inference('sup-', [status(thm)], ['37', '38'])).
% 14.03/14.23  thf('40', plain,
% 14.03/14.23      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 14.03/14.23      inference('sup+', [status(thm)], ['36', '39'])).
% 14.03/14.23  thf(commutativity_k3_xboole_0, axiom,
% 14.03/14.23    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 14.03/14.23  thf('41', plain,
% 14.03/14.23      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 14.03/14.23      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 14.03/14.23  thf('42', plain,
% 14.03/14.23      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 14.03/14.23      inference('sup+', [status(thm)], ['40', '41'])).
% 14.03/14.23  thf('43', plain,
% 14.03/14.23      (![X0 : $i, X1 : $i]:
% 14.03/14.23         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 14.03/14.23      inference('demod', [status(thm)], ['35', '42'])).
% 14.03/14.23  thf('44', plain,
% 14.03/14.23      (![X0 : $i, X1 : $i]:
% 14.03/14.23         ((k1_xboole_0) = (k9_subset_1 @ X0 @ k1_xboole_0 @ X1))),
% 14.03/14.23      inference('demod', [status(thm)], ['32', '43'])).
% 14.03/14.23  thf('45', plain,
% 14.03/14.23      (![X0 : $i, X1 : $i]:
% 14.03/14.23         (~ (l1_pre_topc @ X0)
% 14.03/14.23          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 14.03/14.23          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 14.03/14.23          | ~ (v4_pre_topc @ X1 @ X0)
% 14.03/14.23          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 14.03/14.23      inference('demod', [status(thm)], ['29', '44'])).
% 14.03/14.23  thf('46', plain,
% 14.03/14.23      (![X0 : $i]:
% 14.03/14.23         (~ (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 14.03/14.23          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 14.03/14.23          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 14.03/14.23          | ~ (l1_pre_topc @ X0))),
% 14.03/14.23      inference('sup-', [status(thm)], ['26', '45'])).
% 14.03/14.23  thf('47', plain,
% 14.03/14.23      (![X0 : $i]:
% 14.03/14.23         (~ (v4_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 14.03/14.23          | ~ (l1_struct_0 @ X0)
% 14.03/14.23          | ~ (l1_pre_topc @ X0)
% 14.03/14.23          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 14.03/14.23          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0)))),
% 14.03/14.23      inference('sup-', [status(thm)], ['23', '46'])).
% 14.03/14.23  thf('48', plain,
% 14.03/14.23      (![X0 : $i]:
% 14.03/14.23         (~ (v2_pre_topc @ X0)
% 14.03/14.23          | ~ (l1_pre_topc @ X0)
% 14.03/14.23          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 14.03/14.23          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 14.03/14.23          | ~ (l1_pre_topc @ X0)
% 14.03/14.23          | ~ (l1_struct_0 @ X0))),
% 14.03/14.23      inference('sup-', [status(thm)], ['22', '47'])).
% 14.03/14.23  thf('49', plain,
% 14.03/14.23      (![X0 : $i]:
% 14.03/14.23         (~ (l1_struct_0 @ X0)
% 14.03/14.23          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 14.03/14.23          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 14.03/14.23          | ~ (l1_pre_topc @ X0)
% 14.03/14.23          | ~ (v2_pre_topc @ X0))),
% 14.03/14.23      inference('simplify', [status(thm)], ['48'])).
% 14.03/14.23  thf('50', plain,
% 14.03/14.23      ((((k1_xboole_0) != (k1_xboole_0))
% 14.03/14.23        | ~ (v1_xboole_0 @ k1_xboole_0)
% 14.03/14.23        | ~ (v2_pre_topc @ sk_A)
% 14.03/14.23        | ~ (l1_pre_topc @ sk_A)
% 14.03/14.23        | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 14.03/14.23        | ~ (l1_struct_0 @ sk_A))),
% 14.03/14.23      inference('sup-', [status(thm)], ['21', '49'])).
% 14.03/14.23  thf('51', plain, ((v1_xboole_0 @ sk_B)),
% 14.03/14.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.23  thf('52', plain, (((sk_B) = (k1_xboole_0))),
% 14.03/14.23      inference('sup-', [status(thm)], ['1', '2'])).
% 14.03/14.23  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 14.03/14.23      inference('demod', [status(thm)], ['51', '52'])).
% 14.03/14.23  thf('54', plain, ((v2_pre_topc @ sk_A)),
% 14.03/14.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.23  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 14.03/14.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.23  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 14.03/14.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.23  thf(dt_l1_pre_topc, axiom,
% 14.03/14.23    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 14.03/14.23  thf('57', plain,
% 14.03/14.23      (![X22 : $i]: ((l1_struct_0 @ X22) | ~ (l1_pre_topc @ X22))),
% 14.03/14.23      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 14.03/14.23  thf('58', plain, ((l1_struct_0 @ sk_A)),
% 14.03/14.23      inference('sup-', [status(thm)], ['56', '57'])).
% 14.03/14.23  thf('59', plain,
% 14.03/14.23      ((((k1_xboole_0) != (k1_xboole_0)) | (v2_tex_2 @ k1_xboole_0 @ sk_A))),
% 14.03/14.23      inference('demod', [status(thm)], ['50', '53', '54', '55', '58'])).
% 14.03/14.23  thf('60', plain, ((v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 14.03/14.23      inference('simplify', [status(thm)], ['59'])).
% 14.03/14.23  thf('61', plain, ($false), inference('demod', [status(thm)], ['4', '60'])).
% 14.03/14.23  
% 14.03/14.23  % SZS output end Refutation
% 14.03/14.23  
% 14.03/14.24  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
