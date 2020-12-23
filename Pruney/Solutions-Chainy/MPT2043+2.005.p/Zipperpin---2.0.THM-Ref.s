%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.E5UeKVMa3n

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:37 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 189 expanded)
%              Number of leaves         :   34 (  78 expanded)
%              Depth                    :   15
%              Number of atoms          :  739 (1622 expanded)
%              Number of equality atoms :   45 (  94 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(sk_C_4_type,type,(
    sk_C_4: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t2_yellow19,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) )
            & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) )
            & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) )
         => ! [C: $i] :
              ~ ( ( r2_hidden @ C @ B )
                & ( v1_xboole_0 @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) )
              & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) )
              & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) )
           => ! [C: $i] :
                ~ ( ( r2_hidden @ C @ B )
                  & ( v1_xboole_0 @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t2_yellow19])).

thf('0',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X21: $i] :
      ( ( k3_yellow_1 @ X21 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf(t1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) )
        = ( k1_yellow_1 @ A ) )
      & ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) )
        = A ) ) )).

thf('2',plain,(
    ! [X19: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('3',plain,(
    v1_subset_1 @ sk_B_2 @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('4',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('5',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X21: $i] :
      ( ( k3_yellow_1 @ X21 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('7',plain,(
    ! [X19: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('8',plain,(
    ! [X18: $i] :
      ( ( k9_setfam_1 @ X18 )
      = ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('9',plain,(
    m1_subset_1 @ sk_B_2 @ ( k9_setfam_1 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6','7','8'])).

thf(t49_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ! [C: $i] :
            ( ( m1_subset_1 @ C @ A )
           => ( r2_hidden @ C @ B ) )
       => ( A = B ) ) ) )).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( sk_C_2 @ X13 @ X14 ) @ X14 )
      | ( X14 = X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('11',plain,(
    ! [X18: $i] :
      ( ( k9_setfam_1 @ X18 )
      = ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('12',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( sk_C_2 @ X13 @ X14 ) @ X14 )
      | ( X14 = X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k9_setfam_1 @ X14 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( ( k9_setfam_1 @ sk_A )
      = sk_B_2 )
    | ( m1_subset_1 @ ( sk_C_2 @ sk_B_2 @ ( k9_setfam_1 @ sk_A ) ) @ ( k9_setfam_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r2_hidden @ X16 @ X17 )
      | ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('15',plain,
    ( ( ( k9_setfam_1 @ sk_A )
      = sk_B_2 )
    | ( v1_xboole_0 @ ( k9_setfam_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_C_2 @ sk_B_2 @ ( k9_setfam_1 @ sk_A ) ) @ ( k9_setfam_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ( X10
       != ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('21',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X18: $i] :
      ( ( k9_setfam_1 @ X18 )
      = ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('23',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ ( k9_setfam_1 @ X9 ) )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r2_hidden @ ( sk_C_2 @ sk_B_2 @ ( k9_setfam_1 @ sk_A ) ) @ ( k9_setfam_1 @ sk_A ) )
    | ( ( k9_setfam_1 @ sk_A )
      = sk_B_2 ) ),
    inference(clc,[status(thm)],['15','26'])).

thf('28',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( r1_tarski @ X11 @ X9 )
      | ( X10
       != ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('29',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X18: $i] :
      ( ( k9_setfam_1 @ X18 )
      = ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('31',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k9_setfam_1 @ X9 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k9_setfam_1 @ sk_A )
      = sk_B_2 )
    | ( r1_tarski @ ( sk_C_2 @ sk_B_2 @ ( k9_setfam_1 @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X21: $i] :
      ( ( k3_yellow_1 @ X21 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('35',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t11_waybel_7,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) )
     => ( ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) )
      <=> ! [C: $i,D: $i] :
            ( ( ( r1_tarski @ C @ D )
              & ( r1_tarski @ D @ A )
              & ( r2_hidden @ C @ B ) )
           => ( r2_hidden @ D @ B ) ) ) ) )).

thf('36',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( v13_waybel_0 @ X24 @ ( k3_yellow_1 @ X25 ) )
      | ~ ( r2_hidden @ X26 @ X24 )
      | ~ ( r1_tarski @ X26 @ X27 )
      | ~ ( r1_tarski @ X27 @ X25 )
      | ( r2_hidden @ X27 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X25 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t11_waybel_7])).

thf('37',plain,(
    ! [X21: $i] :
      ( ( k3_yellow_1 @ X21 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('38',plain,(
    ! [X21: $i] :
      ( ( k3_yellow_1 @ X21 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('39',plain,(
    ! [X19: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('40',plain,(
    ! [X18: $i] :
      ( ( k9_setfam_1 @ X18 )
      = ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('41',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( v13_waybel_0 @ X24 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X25 ) ) )
      | ~ ( r2_hidden @ X26 @ X24 )
      | ~ ( r1_tarski @ X26 @ X27 )
      | ~ ( r1_tarski @ X27 @ X25 )
      | ( r2_hidden @ X27 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k9_setfam_1 @ ( k9_setfam_1 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['36','37','38','39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_B_2 @ ( k9_setfam_1 @ ( k9_setfam_1 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['35','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_B_2 @ ( k9_setfam_1 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6','7','8'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k9_setfam_1 @ sk_A )
        = sk_B_2 )
      | ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( r1_tarski @ X0 @ ( sk_C_2 @ sk_B_2 @ ( k9_setfam_1 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_C_2 @ sk_B_2 @ ( k9_setfam_1 @ sk_A ) ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['32','44'])).

thf('46',plain,
    ( ( r2_hidden @ ( sk_C_2 @ sk_B_2 @ ( k9_setfam_1 @ sk_A ) ) @ sk_B_2 )
    | ~ ( r2_hidden @ k1_xboole_0 @ sk_B_2 )
    | ( ( k9_setfam_1 @ sk_A )
      = sk_B_2 ) ),
    inference('sup-',[status(thm)],['4','45'])).

thf('47',plain,(
    r2_hidden @ sk_C_4 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( r2_hidden @ k1_xboole_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ k1_xboole_0 @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,
    ( ( r2_hidden @ k1_xboole_0 @ sk_B_2 )
    | ~ ( v1_xboole_0 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['47','54'])).

thf('56',plain,(
    v1_xboole_0 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    r2_hidden @ k1_xboole_0 @ sk_B_2 ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( r2_hidden @ ( sk_C_2 @ sk_B_2 @ ( k9_setfam_1 @ sk_A ) ) @ sk_B_2 )
    | ( ( k9_setfam_1 @ sk_A )
      = sk_B_2 ) ),
    inference(demod,[status(thm)],['46','57'])).

thf('59',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( sk_C_2 @ X13 @ X14 ) @ X13 )
      | ( X14 = X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('60',plain,(
    ! [X18: $i] :
      ( ( k9_setfam_1 @ X18 )
      = ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('61',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( sk_C_2 @ X13 @ X14 ) @ X13 )
      | ( X14 = X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k9_setfam_1 @ X14 ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( k9_setfam_1 @ sk_A )
      = sk_B_2 )
    | ~ ( m1_subset_1 @ sk_B_2 @ ( k9_setfam_1 @ ( k9_setfam_1 @ sk_A ) ) )
    | ( ( k9_setfam_1 @ sk_A )
      = sk_B_2 ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_B_2 @ ( k9_setfam_1 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6','7','8'])).

thf('64',plain,
    ( ( ( k9_setfam_1 @ sk_A )
      = sk_B_2 )
    | ( ( k9_setfam_1 @ sk_A )
      = sk_B_2 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k9_setfam_1 @ sk_A )
    = sk_B_2 ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    v1_subset_1 @ sk_B_2 @ sk_B_2 ),
    inference(demod,[status(thm)],['3','65'])).

thf(rc3_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ~ ( v1_subset_1 @ B @ A )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('67',plain,(
    ! [X15: $i] :
      ~ ( v1_subset_1 @ ( sk_B_1 @ X15 ) @ X15 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('68',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X15 ) @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('69',plain,(
    ! [X18: $i] :
      ( ( k9_setfam_1 @ X18 )
      = ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('70',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X15 ) @ ( k9_setfam_1 @ X15 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('71',plain,(
    ! [X22: $i,X23: $i] :
      ( ( X23 = X22 )
      | ( v1_subset_1 @ X23 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('72',plain,(
    ! [X18: $i] :
      ( ( k9_setfam_1 @ X18 )
      = ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('73',plain,(
    ! [X22: $i,X23: $i] :
      ( ( X23 = X22 )
      | ( v1_subset_1 @ X23 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k9_setfam_1 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v1_subset_1 @ ( sk_B_1 @ X0 ) @ X0 )
      | ( ( sk_B_1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X15: $i] :
      ~ ( v1_subset_1 @ ( sk_B_1 @ X15 ) @ X15 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 @ X0 )
      = X0 ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X15: $i] :
      ~ ( v1_subset_1 @ X15 @ X15 ) ),
    inference(demod,[status(thm)],['67','76'])).

thf('78',plain,(
    $false ),
    inference('sup-',[status(thm)],['66','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.E5UeKVMa3n
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:45:17 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.62  % Solved by: fo/fo7.sh
% 0.39/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.62  % done 332 iterations in 0.166s
% 0.39/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.62  % SZS output start Refutation
% 0.39/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.62  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.39/0.62  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.39/0.62  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.39/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.62  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.39/0.62  thf(sk_C_4_type, type, sk_C_4: $i).
% 0.39/0.62  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.39/0.62  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.39/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.39/0.62  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.39/0.62  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.39/0.62  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.39/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.62  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.39/0.62  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.39/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.39/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.62  thf(t2_yellow19, conjecture,
% 0.39/0.62    (![A:$i]:
% 0.39/0.62     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.39/0.62       ( ![B:$i]:
% 0.39/0.62         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.39/0.62             ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 0.39/0.62             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.39/0.62             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.39/0.62             ( m1_subset_1 @
% 0.39/0.62               B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 0.39/0.62           ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ))).
% 0.39/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.62    (~( ![A:$i]:
% 0.39/0.62        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.39/0.62          ( ![B:$i]:
% 0.39/0.62            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.39/0.62                ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 0.39/0.62                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.39/0.62                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.39/0.62                ( m1_subset_1 @
% 0.39/0.62                  B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 0.39/0.62              ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ) )),
% 0.39/0.62    inference('cnf.neg', [status(esa)], [t2_yellow19])).
% 0.39/0.62  thf('0', plain,
% 0.39/0.62      ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(t4_yellow_1, axiom,
% 0.39/0.62    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ))).
% 0.39/0.62  thf('1', plain,
% 0.39/0.62      (![X21 : $i]: ((k3_yellow_1 @ X21) = (k2_yellow_1 @ (k9_setfam_1 @ X21)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.39/0.62  thf(t1_yellow_1, axiom,
% 0.39/0.62    (![A:$i]:
% 0.39/0.62     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.39/0.62       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.39/0.62  thf('2', plain, (![X19 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X19)) = (X19))),
% 0.39/0.62      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.39/0.62  thf('3', plain, ((v1_subset_1 @ sk_B_2 @ (k9_setfam_1 @ sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['0', '1', '2'])).
% 0.39/0.62  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.39/0.62  thf('4', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.39/0.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.39/0.62  thf('5', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_B_2 @ 
% 0.39/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ sk_A))))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('6', plain,
% 0.39/0.62      (![X21 : $i]: ((k3_yellow_1 @ X21) = (k2_yellow_1 @ (k9_setfam_1 @ X21)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.39/0.62  thf('7', plain, (![X19 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X19)) = (X19))),
% 0.39/0.62      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.39/0.62  thf(redefinition_k9_setfam_1, axiom,
% 0.39/0.62    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 0.39/0.62  thf('8', plain, (![X18 : $i]: ((k9_setfam_1 @ X18) = (k1_zfmisc_1 @ X18))),
% 0.39/0.62      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.39/0.62  thf('9', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_B_2 @ (k9_setfam_1 @ (k9_setfam_1 @ sk_A)))),
% 0.39/0.62      inference('demod', [status(thm)], ['5', '6', '7', '8'])).
% 0.39/0.62  thf(t49_subset_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.62       ( ( ![C:$i]: ( ( m1_subset_1 @ C @ A ) => ( r2_hidden @ C @ B ) ) ) =>
% 0.39/0.62         ( ( A ) = ( B ) ) ) ))).
% 0.39/0.62  thf('10', plain,
% 0.39/0.62      (![X13 : $i, X14 : $i]:
% 0.39/0.62         ((m1_subset_1 @ (sk_C_2 @ X13 @ X14) @ X14)
% 0.39/0.62          | ((X14) = (X13))
% 0.39/0.62          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t49_subset_1])).
% 0.39/0.62  thf('11', plain, (![X18 : $i]: ((k9_setfam_1 @ X18) = (k1_zfmisc_1 @ X18))),
% 0.39/0.62      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.39/0.62  thf('12', plain,
% 0.39/0.62      (![X13 : $i, X14 : $i]:
% 0.39/0.62         ((m1_subset_1 @ (sk_C_2 @ X13 @ X14) @ X14)
% 0.39/0.62          | ((X14) = (X13))
% 0.39/0.62          | ~ (m1_subset_1 @ X13 @ (k9_setfam_1 @ X14)))),
% 0.39/0.62      inference('demod', [status(thm)], ['10', '11'])).
% 0.39/0.62  thf('13', plain,
% 0.39/0.62      ((((k9_setfam_1 @ sk_A) = (sk_B_2))
% 0.39/0.63        | (m1_subset_1 @ (sk_C_2 @ sk_B_2 @ (k9_setfam_1 @ sk_A)) @ 
% 0.39/0.63           (k9_setfam_1 @ sk_A)))),
% 0.39/0.63      inference('sup-', [status(thm)], ['9', '12'])).
% 0.39/0.63  thf(t2_subset, axiom,
% 0.39/0.63    (![A:$i,B:$i]:
% 0.39/0.63     ( ( m1_subset_1 @ A @ B ) =>
% 0.39/0.63       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.39/0.63  thf('14', plain,
% 0.39/0.63      (![X16 : $i, X17 : $i]:
% 0.39/0.63         ((r2_hidden @ X16 @ X17)
% 0.39/0.63          | (v1_xboole_0 @ X17)
% 0.39/0.63          | ~ (m1_subset_1 @ X16 @ X17))),
% 0.39/0.63      inference('cnf', [status(esa)], [t2_subset])).
% 0.39/0.63  thf('15', plain,
% 0.39/0.63      ((((k9_setfam_1 @ sk_A) = (sk_B_2))
% 0.39/0.63        | (v1_xboole_0 @ (k9_setfam_1 @ sk_A))
% 0.39/0.63        | (r2_hidden @ (sk_C_2 @ sk_B_2 @ (k9_setfam_1 @ sk_A)) @ 
% 0.39/0.63           (k9_setfam_1 @ sk_A)))),
% 0.39/0.63      inference('sup-', [status(thm)], ['13', '14'])).
% 0.39/0.63  thf(d3_tarski, axiom,
% 0.39/0.63    (![A:$i,B:$i]:
% 0.39/0.63     ( ( r1_tarski @ A @ B ) <=>
% 0.39/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.39/0.63  thf('16', plain,
% 0.39/0.63      (![X4 : $i, X6 : $i]:
% 0.39/0.63         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.39/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.63  thf('17', plain,
% 0.39/0.63      (![X4 : $i, X6 : $i]:
% 0.39/0.63         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.39/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.63  thf('18', plain,
% 0.39/0.63      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.39/0.63      inference('sup-', [status(thm)], ['16', '17'])).
% 0.39/0.63  thf('19', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.39/0.63      inference('simplify', [status(thm)], ['18'])).
% 0.39/0.63  thf(d1_zfmisc_1, axiom,
% 0.39/0.63    (![A:$i,B:$i]:
% 0.39/0.63     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.39/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.39/0.63  thf('20', plain,
% 0.39/0.63      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.39/0.63         (~ (r1_tarski @ X8 @ X9)
% 0.39/0.63          | (r2_hidden @ X8 @ X10)
% 0.39/0.63          | ((X10) != (k1_zfmisc_1 @ X9)))),
% 0.39/0.63      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.39/0.63  thf('21', plain,
% 0.39/0.63      (![X8 : $i, X9 : $i]:
% 0.39/0.63         ((r2_hidden @ X8 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X8 @ X9))),
% 0.39/0.63      inference('simplify', [status(thm)], ['20'])).
% 0.39/0.63  thf('22', plain, (![X18 : $i]: ((k9_setfam_1 @ X18) = (k1_zfmisc_1 @ X18))),
% 0.39/0.63      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.39/0.63  thf('23', plain,
% 0.39/0.63      (![X8 : $i, X9 : $i]:
% 0.39/0.63         ((r2_hidden @ X8 @ (k9_setfam_1 @ X9)) | ~ (r1_tarski @ X8 @ X9))),
% 0.39/0.63      inference('demod', [status(thm)], ['21', '22'])).
% 0.39/0.63  thf('24', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k9_setfam_1 @ X0))),
% 0.39/0.63      inference('sup-', [status(thm)], ['19', '23'])).
% 0.39/0.63  thf(d1_xboole_0, axiom,
% 0.39/0.63    (![A:$i]:
% 0.39/0.63     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.39/0.63  thf('25', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.39/0.63      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.63  thf('26', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k9_setfam_1 @ X0))),
% 0.39/0.63      inference('sup-', [status(thm)], ['24', '25'])).
% 0.39/0.63  thf('27', plain,
% 0.39/0.63      (((r2_hidden @ (sk_C_2 @ sk_B_2 @ (k9_setfam_1 @ sk_A)) @ 
% 0.39/0.63         (k9_setfam_1 @ sk_A))
% 0.39/0.63        | ((k9_setfam_1 @ sk_A) = (sk_B_2)))),
% 0.39/0.63      inference('clc', [status(thm)], ['15', '26'])).
% 0.39/0.63  thf('28', plain,
% 0.39/0.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.39/0.63         (~ (r2_hidden @ X11 @ X10)
% 0.39/0.63          | (r1_tarski @ X11 @ X9)
% 0.39/0.63          | ((X10) != (k1_zfmisc_1 @ X9)))),
% 0.39/0.63      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.39/0.63  thf('29', plain,
% 0.39/0.63      (![X9 : $i, X11 : $i]:
% 0.39/0.63         ((r1_tarski @ X11 @ X9) | ~ (r2_hidden @ X11 @ (k1_zfmisc_1 @ X9)))),
% 0.39/0.63      inference('simplify', [status(thm)], ['28'])).
% 0.39/0.63  thf('30', plain, (![X18 : $i]: ((k9_setfam_1 @ X18) = (k1_zfmisc_1 @ X18))),
% 0.39/0.63      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.39/0.63  thf('31', plain,
% 0.39/0.63      (![X9 : $i, X11 : $i]:
% 0.39/0.63         ((r1_tarski @ X11 @ X9) | ~ (r2_hidden @ X11 @ (k9_setfam_1 @ X9)))),
% 0.39/0.63      inference('demod', [status(thm)], ['29', '30'])).
% 0.39/0.63  thf('32', plain,
% 0.39/0.63      ((((k9_setfam_1 @ sk_A) = (sk_B_2))
% 0.39/0.63        | (r1_tarski @ (sk_C_2 @ sk_B_2 @ (k9_setfam_1 @ sk_A)) @ sk_A))),
% 0.39/0.63      inference('sup-', [status(thm)], ['27', '31'])).
% 0.39/0.63  thf('33', plain, ((v13_waybel_0 @ sk_B_2 @ (k3_yellow_1 @ sk_A))),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('34', plain,
% 0.39/0.63      (![X21 : $i]: ((k3_yellow_1 @ X21) = (k2_yellow_1 @ (k9_setfam_1 @ X21)))),
% 0.39/0.63      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.39/0.63  thf('35', plain,
% 0.39/0.63      ((v13_waybel_0 @ sk_B_2 @ (k2_yellow_1 @ (k9_setfam_1 @ sk_A)))),
% 0.39/0.63      inference('demod', [status(thm)], ['33', '34'])).
% 0.39/0.63  thf(t11_waybel_7, axiom,
% 0.39/0.63    (![A:$i,B:$i]:
% 0.39/0.63     ( ( m1_subset_1 @
% 0.39/0.63         B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) =>
% 0.39/0.63       ( ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) <=>
% 0.39/0.63         ( ![C:$i,D:$i]:
% 0.39/0.63           ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ D @ A ) & 
% 0.39/0.63               ( r2_hidden @ C @ B ) ) =>
% 0.39/0.63             ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.39/0.63  thf('36', plain,
% 0.39/0.63      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.39/0.63         (~ (v13_waybel_0 @ X24 @ (k3_yellow_1 @ X25))
% 0.39/0.63          | ~ (r2_hidden @ X26 @ X24)
% 0.39/0.63          | ~ (r1_tarski @ X26 @ X27)
% 0.39/0.63          | ~ (r1_tarski @ X27 @ X25)
% 0.39/0.63          | (r2_hidden @ X27 @ X24)
% 0.39/0.63          | ~ (m1_subset_1 @ X24 @ 
% 0.39/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X25)))))),
% 0.39/0.63      inference('cnf', [status(esa)], [t11_waybel_7])).
% 0.39/0.63  thf('37', plain,
% 0.39/0.63      (![X21 : $i]: ((k3_yellow_1 @ X21) = (k2_yellow_1 @ (k9_setfam_1 @ X21)))),
% 0.39/0.63      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.39/0.63  thf('38', plain,
% 0.39/0.63      (![X21 : $i]: ((k3_yellow_1 @ X21) = (k2_yellow_1 @ (k9_setfam_1 @ X21)))),
% 0.39/0.63      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.39/0.63  thf('39', plain,
% 0.39/0.63      (![X19 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X19)) = (X19))),
% 0.39/0.63      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.39/0.63  thf('40', plain, (![X18 : $i]: ((k9_setfam_1 @ X18) = (k1_zfmisc_1 @ X18))),
% 0.39/0.63      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.39/0.63  thf('41', plain,
% 0.39/0.63      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.39/0.63         (~ (v13_waybel_0 @ X24 @ (k2_yellow_1 @ (k9_setfam_1 @ X25)))
% 0.39/0.63          | ~ (r2_hidden @ X26 @ X24)
% 0.39/0.63          | ~ (r1_tarski @ X26 @ X27)
% 0.39/0.63          | ~ (r1_tarski @ X27 @ X25)
% 0.39/0.63          | (r2_hidden @ X27 @ X24)
% 0.39/0.63          | ~ (m1_subset_1 @ X24 @ (k9_setfam_1 @ (k9_setfam_1 @ X25))))),
% 0.39/0.63      inference('demod', [status(thm)], ['36', '37', '38', '39', '40'])).
% 0.39/0.63  thf('42', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]:
% 0.39/0.63         (~ (m1_subset_1 @ sk_B_2 @ (k9_setfam_1 @ (k9_setfam_1 @ sk_A)))
% 0.39/0.63          | (r2_hidden @ X0 @ sk_B_2)
% 0.39/0.63          | ~ (r1_tarski @ X0 @ sk_A)
% 0.39/0.63          | ~ (r1_tarski @ X1 @ X0)
% 0.39/0.63          | ~ (r2_hidden @ X1 @ sk_B_2))),
% 0.39/0.63      inference('sup-', [status(thm)], ['35', '41'])).
% 0.39/0.63  thf('43', plain,
% 0.39/0.63      ((m1_subset_1 @ sk_B_2 @ (k9_setfam_1 @ (k9_setfam_1 @ sk_A)))),
% 0.39/0.63      inference('demod', [status(thm)], ['5', '6', '7', '8'])).
% 0.39/0.63  thf('44', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]:
% 0.39/0.63         ((r2_hidden @ X0 @ sk_B_2)
% 0.39/0.63          | ~ (r1_tarski @ X0 @ sk_A)
% 0.39/0.63          | ~ (r1_tarski @ X1 @ X0)
% 0.39/0.63          | ~ (r2_hidden @ X1 @ sk_B_2))),
% 0.39/0.63      inference('demod', [status(thm)], ['42', '43'])).
% 0.39/0.63  thf('45', plain,
% 0.39/0.63      (![X0 : $i]:
% 0.39/0.63         (((k9_setfam_1 @ sk_A) = (sk_B_2))
% 0.39/0.63          | ~ (r2_hidden @ X0 @ sk_B_2)
% 0.39/0.63          | ~ (r1_tarski @ X0 @ (sk_C_2 @ sk_B_2 @ (k9_setfam_1 @ sk_A)))
% 0.39/0.63          | (r2_hidden @ (sk_C_2 @ sk_B_2 @ (k9_setfam_1 @ sk_A)) @ sk_B_2))),
% 0.39/0.63      inference('sup-', [status(thm)], ['32', '44'])).
% 0.39/0.63  thf('46', plain,
% 0.39/0.63      (((r2_hidden @ (sk_C_2 @ sk_B_2 @ (k9_setfam_1 @ sk_A)) @ sk_B_2)
% 0.39/0.63        | ~ (r2_hidden @ k1_xboole_0 @ sk_B_2)
% 0.39/0.63        | ((k9_setfam_1 @ sk_A) = (sk_B_2)))),
% 0.39/0.63      inference('sup-', [status(thm)], ['4', '45'])).
% 0.39/0.63  thf('47', plain, ((r2_hidden @ sk_C_4 @ sk_B_2)),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('48', plain,
% 0.39/0.63      (![X4 : $i, X6 : $i]:
% 0.39/0.63         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.39/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.63  thf('49', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.39/0.63      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.63  thf('50', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.39/0.63      inference('sup-', [status(thm)], ['48', '49'])).
% 0.39/0.63  thf('51', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.39/0.63      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.39/0.63  thf('52', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]:
% 0.39/0.63         ((r2_hidden @ X0 @ sk_B_2)
% 0.39/0.63          | ~ (r1_tarski @ X0 @ sk_A)
% 0.39/0.63          | ~ (r1_tarski @ X1 @ X0)
% 0.39/0.63          | ~ (r2_hidden @ X1 @ sk_B_2))),
% 0.39/0.63      inference('demod', [status(thm)], ['42', '43'])).
% 0.39/0.63  thf('53', plain,
% 0.39/0.63      (![X0 : $i]:
% 0.39/0.63         (~ (r2_hidden @ X0 @ sk_B_2)
% 0.39/0.63          | ~ (r1_tarski @ X0 @ k1_xboole_0)
% 0.39/0.63          | (r2_hidden @ k1_xboole_0 @ sk_B_2))),
% 0.39/0.63      inference('sup-', [status(thm)], ['51', '52'])).
% 0.39/0.63  thf('54', plain,
% 0.39/0.63      (![X0 : $i]:
% 0.39/0.63         (~ (v1_xboole_0 @ X0)
% 0.39/0.63          | (r2_hidden @ k1_xboole_0 @ sk_B_2)
% 0.39/0.63          | ~ (r2_hidden @ X0 @ sk_B_2))),
% 0.39/0.63      inference('sup-', [status(thm)], ['50', '53'])).
% 0.39/0.63  thf('55', plain,
% 0.39/0.63      (((r2_hidden @ k1_xboole_0 @ sk_B_2) | ~ (v1_xboole_0 @ sk_C_4))),
% 0.39/0.63      inference('sup-', [status(thm)], ['47', '54'])).
% 0.39/0.63  thf('56', plain, ((v1_xboole_0 @ sk_C_4)),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('57', plain, ((r2_hidden @ k1_xboole_0 @ sk_B_2)),
% 0.39/0.63      inference('demod', [status(thm)], ['55', '56'])).
% 0.39/0.63  thf('58', plain,
% 0.39/0.63      (((r2_hidden @ (sk_C_2 @ sk_B_2 @ (k9_setfam_1 @ sk_A)) @ sk_B_2)
% 0.39/0.63        | ((k9_setfam_1 @ sk_A) = (sk_B_2)))),
% 0.39/0.63      inference('demod', [status(thm)], ['46', '57'])).
% 0.39/0.63  thf('59', plain,
% 0.39/0.63      (![X13 : $i, X14 : $i]:
% 0.39/0.63         (~ (r2_hidden @ (sk_C_2 @ X13 @ X14) @ X13)
% 0.39/0.63          | ((X14) = (X13))
% 0.39/0.63          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.39/0.63      inference('cnf', [status(esa)], [t49_subset_1])).
% 0.39/0.63  thf('60', plain, (![X18 : $i]: ((k9_setfam_1 @ X18) = (k1_zfmisc_1 @ X18))),
% 0.39/0.63      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.39/0.63  thf('61', plain,
% 0.39/0.63      (![X13 : $i, X14 : $i]:
% 0.39/0.63         (~ (r2_hidden @ (sk_C_2 @ X13 @ X14) @ X13)
% 0.39/0.63          | ((X14) = (X13))
% 0.39/0.63          | ~ (m1_subset_1 @ X13 @ (k9_setfam_1 @ X14)))),
% 0.39/0.63      inference('demod', [status(thm)], ['59', '60'])).
% 0.39/0.63  thf('62', plain,
% 0.39/0.63      ((((k9_setfam_1 @ sk_A) = (sk_B_2))
% 0.39/0.63        | ~ (m1_subset_1 @ sk_B_2 @ (k9_setfam_1 @ (k9_setfam_1 @ sk_A)))
% 0.39/0.63        | ((k9_setfam_1 @ sk_A) = (sk_B_2)))),
% 0.39/0.63      inference('sup-', [status(thm)], ['58', '61'])).
% 0.39/0.63  thf('63', plain,
% 0.39/0.63      ((m1_subset_1 @ sk_B_2 @ (k9_setfam_1 @ (k9_setfam_1 @ sk_A)))),
% 0.39/0.63      inference('demod', [status(thm)], ['5', '6', '7', '8'])).
% 0.39/0.63  thf('64', plain,
% 0.39/0.63      ((((k9_setfam_1 @ sk_A) = (sk_B_2)) | ((k9_setfam_1 @ sk_A) = (sk_B_2)))),
% 0.39/0.63      inference('demod', [status(thm)], ['62', '63'])).
% 0.39/0.63  thf('65', plain, (((k9_setfam_1 @ sk_A) = (sk_B_2))),
% 0.39/0.63      inference('simplify', [status(thm)], ['64'])).
% 0.39/0.63  thf('66', plain, ((v1_subset_1 @ sk_B_2 @ sk_B_2)),
% 0.39/0.63      inference('demod', [status(thm)], ['3', '65'])).
% 0.39/0.63  thf(rc3_subset_1, axiom,
% 0.39/0.63    (![A:$i]:
% 0.39/0.63     ( ?[B:$i]:
% 0.39/0.63       ( ( ~( v1_subset_1 @ B @ A ) ) & 
% 0.39/0.63         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.39/0.63  thf('67', plain, (![X15 : $i]: ~ (v1_subset_1 @ (sk_B_1 @ X15) @ X15)),
% 0.39/0.63      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.39/0.63  thf('68', plain,
% 0.39/0.63      (![X15 : $i]: (m1_subset_1 @ (sk_B_1 @ X15) @ (k1_zfmisc_1 @ X15))),
% 0.39/0.63      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.39/0.63  thf('69', plain, (![X18 : $i]: ((k9_setfam_1 @ X18) = (k1_zfmisc_1 @ X18))),
% 0.39/0.63      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.39/0.63  thf('70', plain,
% 0.39/0.63      (![X15 : $i]: (m1_subset_1 @ (sk_B_1 @ X15) @ (k9_setfam_1 @ X15))),
% 0.39/0.63      inference('demod', [status(thm)], ['68', '69'])).
% 0.39/0.63  thf(d7_subset_1, axiom,
% 0.39/0.63    (![A:$i,B:$i]:
% 0.39/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.63       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.39/0.63  thf('71', plain,
% 0.39/0.63      (![X22 : $i, X23 : $i]:
% 0.39/0.63         (((X23) = (X22))
% 0.39/0.63          | (v1_subset_1 @ X23 @ X22)
% 0.39/0.63          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 0.39/0.63      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.39/0.63  thf('72', plain, (![X18 : $i]: ((k9_setfam_1 @ X18) = (k1_zfmisc_1 @ X18))),
% 0.39/0.63      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.39/0.63  thf('73', plain,
% 0.39/0.63      (![X22 : $i, X23 : $i]:
% 0.39/0.63         (((X23) = (X22))
% 0.39/0.63          | (v1_subset_1 @ X23 @ X22)
% 0.39/0.63          | ~ (m1_subset_1 @ X23 @ (k9_setfam_1 @ X22)))),
% 0.39/0.63      inference('demod', [status(thm)], ['71', '72'])).
% 0.39/0.63  thf('74', plain,
% 0.39/0.63      (![X0 : $i]:
% 0.39/0.63         ((v1_subset_1 @ (sk_B_1 @ X0) @ X0) | ((sk_B_1 @ X0) = (X0)))),
% 0.39/0.63      inference('sup-', [status(thm)], ['70', '73'])).
% 0.39/0.63  thf('75', plain, (![X15 : $i]: ~ (v1_subset_1 @ (sk_B_1 @ X15) @ X15)),
% 0.39/0.63      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.39/0.63  thf('76', plain, (![X0 : $i]: ((sk_B_1 @ X0) = (X0))),
% 0.39/0.63      inference('clc', [status(thm)], ['74', '75'])).
% 0.39/0.63  thf('77', plain, (![X15 : $i]: ~ (v1_subset_1 @ X15 @ X15)),
% 0.39/0.63      inference('demod', [status(thm)], ['67', '76'])).
% 0.39/0.63  thf('78', plain, ($false), inference('sup-', [status(thm)], ['66', '77'])).
% 0.39/0.63  
% 0.39/0.63  % SZS output end Refutation
% 0.39/0.63  
% 0.50/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
