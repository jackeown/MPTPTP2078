%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1111+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TeC9M3Uc9b

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:06 EST 2020

% Result     : Theorem 1.85s
% Output     : Refutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   59 (  72 expanded)
%              Number of leaves         :   25 (  33 expanded)
%              Depth                    :   12
%              Number of atoms          :  247 ( 386 expanded)
%              Number of equality atoms :   16 (  27 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_B_118_type,type,(
    sk_B_118: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_25_type,type,(
    sk_A_25: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ ( B @ A ) ) ) )).

thf('0',plain,(
    ! [X12: $i] :
      ( ( v1_xboole_0 @ X12 )
      | ( r2_hidden @ ( sk_B @ X12 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('1',plain,(
    ! [X12: $i] :
      ( ( v1_xboole_0 @ X12 )
      | ( r2_hidden @ ( sk_B @ X12 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t41_pre_topc,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ~ ( ( B
               != ( k1_struct_0 @ A ) )
              & ! [C: $i] :
                  ( ( m1_subset_1 @ ( C @ ( u1_struct_0 @ A ) ) )
                 => ~ ( r2_hidden @ ( C @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ~ ( ( B
                 != ( k1_struct_0 @ A ) )
                & ! [C: $i] :
                    ( ( m1_subset_1 @ ( C @ ( u1_struct_0 @ A ) ) )
                   => ~ ( r2_hidden @ ( C @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t41_pre_topc])).

thf('2',plain,(
    m1_subset_1 @ ( sk_B_118 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A_25 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X4951: $i] :
      ( ( k9_setfam_1 @ X4951 )
      = ( k1_zfmisc_1 @ X4951 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('4',plain,(
    m1_subset_1 @ ( sk_B_118 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A_25 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( A @ ( k1_zfmisc_1 @ B ) ) )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('5',plain,(
    ! [X1964: $i,X1965: $i] :
      ( ( r1_tarski @ ( X1964 @ X1965 ) )
      | ~ ( m1_subset_1 @ ( X1964 @ ( k1_zfmisc_1 @ X1965 ) ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('6',plain,(
    ! [X4951: $i] :
      ( ( k9_setfam_1 @ X4951 )
      = ( k1_zfmisc_1 @ X4951 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('7',plain,(
    ! [X1964: $i,X1965: $i] :
      ( ( r1_tarski @ ( X1964 @ X1965 ) )
      | ~ ( m1_subset_1 @ ( X1964 @ ( k9_setfam_1 @ X1965 ) ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ ( sk_B_118 @ ( u1_struct_0 @ sk_A_25 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ A ) )
         => ( r2_hidden @ ( C @ B ) ) ) ) )).

thf('9',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ ( X13 @ X14 ) )
      | ( r2_hidden @ ( X13 @ X15 ) )
      | ~ ( r1_tarski @ ( X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( X0 @ ( u1_struct_0 @ sk_A_25 ) ) )
      | ~ ( r2_hidden @ ( X0 @ sk_B_118 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( v1_xboole_0 @ sk_B_118 )
    | ( r2_hidden @ ( sk_B @ sk_B_118 @ ( u1_struct_0 @ sk_A_25 ) ) ) ),
    inference('sup-',[status(thm)],['1','10'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ ( A @ B ) )
     => ( m1_subset_1 @ ( A @ B ) ) ) )).

thf('12',plain,(
    ! [X1932: $i,X1933: $i] :
      ( ( m1_subset_1 @ ( X1932 @ X1933 ) )
      | ~ ( r2_hidden @ ( X1932 @ X1933 ) ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('13',plain,
    ( ( v1_xboole_0 @ sk_B_118 )
    | ( m1_subset_1 @ ( sk_B @ sk_B_118 @ ( u1_struct_0 @ sk_A_25 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X5963: $i] :
      ( ~ ( r2_hidden @ ( X5963 @ sk_B_118 ) )
      | ~ ( m1_subset_1 @ ( X5963 @ ( u1_struct_0 @ sk_A_25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v1_xboole_0 @ sk_B_118 )
    | ~ ( r2_hidden @ ( sk_B @ sk_B_118 @ sk_B_118 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ ( X10 @ X11 ) )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('17',plain,(
    ~ ( r2_hidden @ ( sk_B @ sk_B_118 @ sk_B_118 ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    v1_xboole_0 @ sk_B_118 ),
    inference('sup-',[status(thm)],['0','17'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('19',plain,(
    ! [X46: $i] :
      ( ( X46 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('20',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('21',plain,(
    ! [X46: $i] :
      ( ( X46 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X46 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    sk_B_118 = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    sk_B_118
 != ( k1_struct_0 @ sk_A_25 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_A_25 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('25',plain,(
    ! [X5907: $i] :
      ( ( l1_struct_0 @ X5907 )
      | ~ ( l1_pre_topc @ X5907 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('26',plain,(
    l1_struct_0 @ sk_A_25 ),
    inference('sup-',[status(thm)],['24','25'])).

thf(fc3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( v1_xboole_0 @ ( k1_struct_0 @ A ) ) ) )).

thf('27',plain,(
    ! [X5922: $i] :
      ( ( v1_xboole_0 @ ( k1_struct_0 @ X5922 ) )
      | ~ ( l1_struct_0 @ X5922 ) ) ),
    inference(cnf,[status(esa)],[fc3_struct_0])).

thf('28',plain,(
    ! [X46: $i] :
      ( ( X46 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X46 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k1_struct_0 @ X0 )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k1_struct_0 @ sk_A_25 )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    sk_B_118 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['23','30'])).

thf('32',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['22','31'])).

%------------------------------------------------------------------------------
