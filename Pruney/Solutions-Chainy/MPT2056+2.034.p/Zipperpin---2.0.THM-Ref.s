%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7X5Zo8A0HN

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:45 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 206 expanded)
%              Number of leaves         :   38 (  88 expanded)
%              Depth                    :   18
%              Number of atoms          :  819 (2320 expanded)
%              Number of equality atoms :   47 ( 134 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t15_yellow19,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) )
            & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
            & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) )
         => ( B
            = ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_struct_0 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) )
              & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
              & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) )
           => ( B
              = ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t15_yellow19])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X15: $i] :
      ( ( ( k2_struct_0 @ X15 )
        = ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X7 @ ( k1_tarski @ X8 ) )
        = X7 )
      | ( r2_hidden @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('3',plain,(
    sk_B_1
 != ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('5',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('6',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t14_yellow19,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
            & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) )
         => ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ ( k1_tarski @ k1_xboole_0 ) )
            = ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) )).

thf('7',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( v2_waybel_0 @ X19 @ ( k3_yellow_1 @ ( k2_struct_0 @ X20 ) ) )
      | ~ ( v13_waybel_0 @ X19 @ ( k3_yellow_1 @ ( k2_struct_0 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X20 ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X20 ) ) ) @ X19 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X20 @ ( k3_yellow19 @ X20 @ ( k2_struct_0 @ X20 ) @ X19 ) ) )
      | ~ ( l1_struct_0 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow19])).

thf('8',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('9',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('10',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf(t4_waybel_7,axiom,(
    ! [A: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ A ) )
      = ( k9_setfam_1 @ A ) ) )).

thf('11',plain,(
    ! [X18: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X18 ) )
      = ( k9_setfam_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_waybel_7])).

thf('12',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('13',plain,(
    ! [X18: $i] :
      ( ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X18 ) ) )
      = ( k9_setfam_1 @ X18 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('14',plain,(
    ! [X14: $i] :
      ( ( k9_setfam_1 @ X14 )
      = ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('15',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('16',plain,(
    ! [X18: $i] :
      ( ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X18 ) ) )
      = ( k9_setfam_1 @ X18 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('17',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( v2_waybel_0 @ X19 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X20 ) ) ) )
      | ~ ( v13_waybel_0 @ X19 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X20 ) ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ X20 ) ) ) )
      | ( ( k7_subset_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ X20 ) ) @ X19 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X20 @ ( k3_yellow19 @ X20 @ ( k2_struct_0 @ X20 ) @ X19 ) ) )
      | ~ ( l1_struct_0 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(demod,[status(thm)],['7','8','9','10','13','14','15','16'])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf('19',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('22',plain,(
    ! [X18: $i] :
      ( ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X18 ) ) )
      = ( k9_setfam_1 @ X18 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('23',plain,(
    ! [X14: $i] :
      ( ( k9_setfam_1 @ X14 )
      = ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('24',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['20','21','22','23'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('25',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( ( k7_subset_1 @ X10 @ X9 @ X11 )
        = ( k4_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('26',plain,(
    ! [X14: $i] :
      ( ( k9_setfam_1 @ X14 )
      = ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('27',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k9_setfam_1 @ X10 ) )
      | ( ( k7_subset_1 @ X10 @ X9 @ X11 )
        = ( k4_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) @ sk_B_1 @ X0 )
      = ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['20','21','22','23'])).

thf('30',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('32',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['18','19','28','29','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    sk_B_1
 != ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['3','37'])).

thf('39',plain,
    ( ( sk_B_1 != sk_B_1 )
    | ( r2_hidden @ k1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['2','38'])).

thf('40',plain,(
    r2_hidden @ k1_xboole_0 @ sk_B_1 ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t2_yellow19,axiom,(
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

thf('42',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X21 )
      | ~ ( v1_subset_1 @ X21 @ ( u1_struct_0 @ ( k3_yellow_1 @ X22 ) ) )
      | ~ ( v2_waybel_0 @ X21 @ ( k3_yellow_1 @ X22 ) )
      | ~ ( v13_waybel_0 @ X21 @ ( k3_yellow_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X22 ) ) ) )
      | ~ ( r2_hidden @ X23 @ X21 )
      | ~ ( v1_xboole_0 @ X23 )
      | ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_yellow19])).

thf('43',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('44',plain,(
    ! [X18: $i] :
      ( ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X18 ) ) )
      = ( k9_setfam_1 @ X18 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('45',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('46',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('47',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('48',plain,(
    ! [X18: $i] :
      ( ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X18 ) ) )
      = ( k9_setfam_1 @ X18 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('49',plain,(
    ! [X14: $i] :
      ( ( k9_setfam_1 @ X14 )
      = ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('50',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X21 )
      | ~ ( v1_subset_1 @ X21 @ ( k9_setfam_1 @ X22 ) )
      | ~ ( v2_waybel_0 @ X21 @ ( k3_lattice3 @ ( k1_lattice3 @ X22 ) ) )
      | ~ ( v13_waybel_0 @ X21 @ ( k3_lattice3 @ ( k1_lattice3 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k9_setfam_1 @ ( k9_setfam_1 @ X22 ) ) )
      | ~ ( r2_hidden @ X23 @ X21 )
      | ~ ( v1_xboole_0 @ X23 )
      | ( v1_xboole_0 @ X22 ) ) ),
    inference(demod,[status(thm)],['42','43','44','45','46','47','48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['41','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['20','21','22','23'])).

thf('53',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('54',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('56',plain,(
    ! [X18: $i] :
      ( ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X18 ) ) )
      = ( k9_setfam_1 @ X18 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('57',plain,(
    v1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['51','52','53','57'])).

thf('59',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','58'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('60',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('61',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('62',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','64'])).

thf('66',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','67'])).

thf('69',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('71',plain,(
    ! [X16: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    $false ),
    inference(demod,[status(thm)],['0','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7X5Zo8A0HN
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:05:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 47 iterations in 0.024s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.47  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.20/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.20/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.47  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.20/0.47  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.20/0.47  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.47  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.20/0.47  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.47  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.20/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.47  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.20/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.47  thf(t15_yellow19, conjecture,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.47             ( v1_subset_1 @
% 0.20/0.47               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.20/0.47             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.20/0.47             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.20/0.47             ( m1_subset_1 @
% 0.20/0.47               B @ 
% 0.20/0.47               ( k1_zfmisc_1 @
% 0.20/0.47                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.20/0.47           ( ( B ) =
% 0.20/0.47             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i]:
% 0.20/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.47          ( ![B:$i]:
% 0.20/0.47            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.47                ( v1_subset_1 @
% 0.20/0.47                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.20/0.47                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.20/0.47                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.20/0.47                ( m1_subset_1 @
% 0.20/0.47                  B @ 
% 0.20/0.47                  ( k1_zfmisc_1 @
% 0.20/0.47                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.20/0.47              ( ( B ) =
% 0.20/0.47                ( k2_yellow19 @
% 0.20/0.47                  A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t15_yellow19])).
% 0.20/0.47  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(d3_struct_0, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (![X15 : $i]:
% 0.20/0.47         (((k2_struct_0 @ X15) = (u1_struct_0 @ X15)) | ~ (l1_struct_0 @ X15))),
% 0.20/0.47      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.47  thf(t65_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.20/0.47       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X7 : $i, X8 : $i]:
% 0.20/0.47         (((k4_xboole_0 @ X7 @ (k1_tarski @ X8)) = (X7))
% 0.20/0.47          | (r2_hidden @ X8 @ X7))),
% 0.20/0.47      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (((sk_B_1)
% 0.20/0.47         != (k2_yellow19 @ sk_A @ 
% 0.20/0.47             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      ((v2_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(d2_yellow_1, axiom,
% 0.20/0.47    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.20/0.47      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      ((v2_waybel_0 @ sk_B_1 @ 
% 0.20/0.47        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.20/0.47      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.47  thf(t14_yellow19, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.47             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.20/0.47             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.20/0.47             ( m1_subset_1 @
% 0.20/0.47               B @ 
% 0.20/0.47               ( k1_zfmisc_1 @
% 0.20/0.47                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.20/0.47           ( ( k7_subset_1 @
% 0.20/0.47               ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ 
% 0.20/0.47               ( k1_tarski @ k1_xboole_0 ) ) =
% 0.20/0.47             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (![X19 : $i, X20 : $i]:
% 0.20/0.47         ((v1_xboole_0 @ X19)
% 0.20/0.47          | ~ (v2_waybel_0 @ X19 @ (k3_yellow_1 @ (k2_struct_0 @ X20)))
% 0.20/0.47          | ~ (v13_waybel_0 @ X19 @ (k3_yellow_1 @ (k2_struct_0 @ X20)))
% 0.20/0.47          | ~ (m1_subset_1 @ X19 @ 
% 0.20/0.47               (k1_zfmisc_1 @ 
% 0.20/0.47                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X20)))))
% 0.20/0.47          | ((k7_subset_1 @ 
% 0.20/0.47              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X20))) @ X19 @ 
% 0.20/0.47              (k1_tarski @ k1_xboole_0))
% 0.20/0.47              = (k2_yellow19 @ X20 @ 
% 0.20/0.47                 (k3_yellow19 @ X20 @ (k2_struct_0 @ X20) @ X19)))
% 0.20/0.47          | ~ (l1_struct_0 @ X20)
% 0.20/0.47          | (v2_struct_0 @ X20))),
% 0.20/0.47      inference('cnf', [status(esa)], [t14_yellow19])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.20/0.47      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.20/0.47      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.20/0.47      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.47  thf(t4_waybel_7, axiom,
% 0.20/0.47    (![A:$i]: ( ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) = ( k9_setfam_1 @ A ) ))).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (![X18 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X18)) = (k9_setfam_1 @ X18))),
% 0.20/0.47      inference('cnf', [status(esa)], [t4_waybel_7])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.20/0.47      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X18 : $i]:
% 0.20/0.47         ((u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X18)))
% 0.20/0.47           = (k9_setfam_1 @ X18))),
% 0.20/0.47      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.47  thf(redefinition_k9_setfam_1, axiom,
% 0.20/0.47    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.47  thf('14', plain, (![X14 : $i]: ((k9_setfam_1 @ X14) = (k1_zfmisc_1 @ X14))),
% 0.20/0.47      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.20/0.47      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      (![X18 : $i]:
% 0.20/0.47         ((u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X18)))
% 0.20/0.47           = (k9_setfam_1 @ X18))),
% 0.20/0.47      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (![X19 : $i, X20 : $i]:
% 0.20/0.47         ((v1_xboole_0 @ X19)
% 0.20/0.47          | ~ (v2_waybel_0 @ X19 @ 
% 0.20/0.47               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X20))))
% 0.20/0.47          | ~ (v13_waybel_0 @ X19 @ 
% 0.20/0.47               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X20))))
% 0.20/0.47          | ~ (m1_subset_1 @ X19 @ 
% 0.20/0.47               (k9_setfam_1 @ (k9_setfam_1 @ (k2_struct_0 @ X20))))
% 0.20/0.47          | ((k7_subset_1 @ (k9_setfam_1 @ (k2_struct_0 @ X20)) @ X19 @ 
% 0.20/0.47              (k1_tarski @ k1_xboole_0))
% 0.20/0.47              = (k2_yellow19 @ X20 @ 
% 0.20/0.47                 (k3_yellow19 @ X20 @ (k2_struct_0 @ X20) @ X19)))
% 0.20/0.47          | ~ (l1_struct_0 @ X20)
% 0.20/0.47          | (v2_struct_0 @ X20))),
% 0.20/0.47      inference('demod', [status(thm)],
% 0.20/0.47                ['7', '8', '9', '10', '13', '14', '15', '16'])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | ~ (l1_struct_0 @ sk_A)
% 0.20/0.47        | ((k7_subset_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A)) @ sk_B_1 @ 
% 0.20/0.47            (k1_tarski @ k1_xboole_0))
% 0.20/0.47            = (k2_yellow19 @ sk_A @ 
% 0.20/0.47               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.20/0.47        | ~ (m1_subset_1 @ sk_B_1 @ 
% 0.20/0.47             (k9_setfam_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A))))
% 0.20/0.47        | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.20/0.47             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.20/0.47        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['6', '17'])).
% 0.20/0.47  thf('19', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_B_1 @ 
% 0.20/0.47        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.20/0.47      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      (![X18 : $i]:
% 0.20/0.47         ((u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X18)))
% 0.20/0.47           = (k9_setfam_1 @ X18))),
% 0.20/0.47      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.47  thf('23', plain, (![X14 : $i]: ((k9_setfam_1 @ X14) = (k1_zfmisc_1 @ X14))),
% 0.20/0.47      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.20/0.47  thf('24', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_B_1 @ 
% 0.20/0.47        (k9_setfam_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A))))),
% 0.20/0.47      inference('demod', [status(thm)], ['20', '21', '22', '23'])).
% 0.20/0.47  thf(redefinition_k7_subset_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.47       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.20/0.47  thf('25', plain,
% 0.20/0.47      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.20/0.47          | ((k7_subset_1 @ X10 @ X9 @ X11) = (k4_xboole_0 @ X9 @ X11)))),
% 0.20/0.47      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.20/0.47  thf('26', plain, (![X14 : $i]: ((k9_setfam_1 @ X14) = (k1_zfmisc_1 @ X14))),
% 0.20/0.47      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X9 @ (k9_setfam_1 @ X10))
% 0.20/0.47          | ((k7_subset_1 @ X10 @ X9 @ X11) = (k4_xboole_0 @ X9 @ X11)))),
% 0.20/0.47      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.47  thf('28', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((k7_subset_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A)) @ sk_B_1 @ X0)
% 0.20/0.47           = (k4_xboole_0 @ sk_B_1 @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['24', '27'])).
% 0.20/0.47  thf('29', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_B_1 @ 
% 0.20/0.47        (k9_setfam_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A))))),
% 0.20/0.47      inference('demod', [status(thm)], ['20', '21', '22', '23'])).
% 0.20/0.47  thf('30', plain,
% 0.20/0.47      ((v13_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('31', plain,
% 0.20/0.47      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.20/0.47      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.47  thf('32', plain,
% 0.20/0.47      ((v13_waybel_0 @ sk_B_1 @ 
% 0.20/0.47        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.20/0.47      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.47  thf('33', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.20/0.47            = (k2_yellow19 @ sk_A @ 
% 0.20/0.47               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.20/0.47        | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.47      inference('demod', [status(thm)], ['18', '19', '28', '29', '32'])).
% 0.20/0.47  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('35', plain,
% 0.20/0.47      (((v1_xboole_0 @ sk_B_1)
% 0.20/0.47        | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.20/0.47            = (k2_yellow19 @ sk_A @ 
% 0.20/0.47               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))),
% 0.20/0.47      inference('clc', [status(thm)], ['33', '34'])).
% 0.20/0.47  thf('36', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('37', plain,
% 0.20/0.47      (((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.20/0.47         = (k2_yellow19 @ sk_A @ 
% 0.20/0.47            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.20/0.47      inference('clc', [status(thm)], ['35', '36'])).
% 0.20/0.47  thf('38', plain,
% 0.20/0.47      (((sk_B_1) != (k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0)))),
% 0.20/0.47      inference('demod', [status(thm)], ['3', '37'])).
% 0.20/0.47  thf('39', plain,
% 0.20/0.47      ((((sk_B_1) != (sk_B_1)) | (r2_hidden @ k1_xboole_0 @ sk_B_1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['2', '38'])).
% 0.20/0.47  thf('40', plain, ((r2_hidden @ k1_xboole_0 @ sk_B_1)),
% 0.20/0.47      inference('simplify', [status(thm)], ['39'])).
% 0.20/0.47  thf('41', plain,
% 0.20/0.47      ((v2_waybel_0 @ sk_B_1 @ 
% 0.20/0.47        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.20/0.47      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.47  thf(t2_yellow19, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.47             ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 0.20/0.47             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.20/0.47             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.20/0.47             ( m1_subset_1 @
% 0.20/0.47               B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 0.20/0.47           ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ))).
% 0.20/0.47  thf('42', plain,
% 0.20/0.47      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.47         ((v1_xboole_0 @ X21)
% 0.20/0.47          | ~ (v1_subset_1 @ X21 @ (u1_struct_0 @ (k3_yellow_1 @ X22)))
% 0.20/0.47          | ~ (v2_waybel_0 @ X21 @ (k3_yellow_1 @ X22))
% 0.20/0.47          | ~ (v13_waybel_0 @ X21 @ (k3_yellow_1 @ X22))
% 0.20/0.47          | ~ (m1_subset_1 @ X21 @ 
% 0.20/0.47               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X22))))
% 0.20/0.47          | ~ (r2_hidden @ X23 @ X21)
% 0.20/0.47          | ~ (v1_xboole_0 @ X23)
% 0.20/0.47          | (v1_xboole_0 @ X22))),
% 0.20/0.47      inference('cnf', [status(esa)], [t2_yellow19])).
% 0.20/0.47  thf('43', plain,
% 0.20/0.47      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.20/0.47      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.47  thf('44', plain,
% 0.20/0.47      (![X18 : $i]:
% 0.20/0.47         ((u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X18)))
% 0.20/0.47           = (k9_setfam_1 @ X18))),
% 0.20/0.47      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.47  thf('45', plain,
% 0.20/0.47      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.20/0.47      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.47  thf('46', plain,
% 0.20/0.47      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.20/0.47      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.47  thf('47', plain,
% 0.20/0.47      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.20/0.47      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.47  thf('48', plain,
% 0.20/0.47      (![X18 : $i]:
% 0.20/0.47         ((u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X18)))
% 0.20/0.47           = (k9_setfam_1 @ X18))),
% 0.20/0.47      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.47  thf('49', plain, (![X14 : $i]: ((k9_setfam_1 @ X14) = (k1_zfmisc_1 @ X14))),
% 0.20/0.47      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.20/0.47  thf('50', plain,
% 0.20/0.47      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.47         ((v1_xboole_0 @ X21)
% 0.20/0.47          | ~ (v1_subset_1 @ X21 @ (k9_setfam_1 @ X22))
% 0.20/0.47          | ~ (v2_waybel_0 @ X21 @ (k3_lattice3 @ (k1_lattice3 @ X22)))
% 0.20/0.47          | ~ (v13_waybel_0 @ X21 @ (k3_lattice3 @ (k1_lattice3 @ X22)))
% 0.20/0.47          | ~ (m1_subset_1 @ X21 @ (k9_setfam_1 @ (k9_setfam_1 @ X22)))
% 0.20/0.47          | ~ (r2_hidden @ X23 @ X21)
% 0.20/0.47          | ~ (v1_xboole_0 @ X23)
% 0.20/0.47          | (v1_xboole_0 @ X22))),
% 0.20/0.47      inference('demod', [status(thm)],
% 0.20/0.47                ['42', '43', '44', '45', '46', '47', '48', '49'])).
% 0.20/0.47  thf('51', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.47          | ~ (v1_xboole_0 @ X0)
% 0.20/0.47          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.20/0.47          | ~ (m1_subset_1 @ sk_B_1 @ 
% 0.20/0.47               (k9_setfam_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A))))
% 0.20/0.47          | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.20/0.47               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.20/0.47          | ~ (v1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A)))
% 0.20/0.47          | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['41', '50'])).
% 0.20/0.47  thf('52', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_B_1 @ 
% 0.20/0.47        (k9_setfam_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A))))),
% 0.20/0.47      inference('demod', [status(thm)], ['20', '21', '22', '23'])).
% 0.20/0.47  thf('53', plain,
% 0.20/0.47      ((v13_waybel_0 @ sk_B_1 @ 
% 0.20/0.47        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.20/0.47      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.47  thf('54', plain,
% 0.20/0.47      ((v1_subset_1 @ sk_B_1 @ 
% 0.20/0.47        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('55', plain,
% 0.20/0.47      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.20/0.47      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.47  thf('56', plain,
% 0.20/0.47      (![X18 : $i]:
% 0.20/0.47         ((u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X18)))
% 0.20/0.47           = (k9_setfam_1 @ X18))),
% 0.20/0.47      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.47  thf('57', plain,
% 0.20/0.47      ((v1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A)))),
% 0.20/0.47      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.20/0.47  thf('58', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.47          | ~ (v1_xboole_0 @ X0)
% 0.20/0.47          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.20/0.47          | (v1_xboole_0 @ sk_B_1))),
% 0.20/0.47      inference('demod', [status(thm)], ['51', '52', '53', '57'])).
% 0.20/0.47  thf('59', plain,
% 0.20/0.47      (((v1_xboole_0 @ sk_B_1)
% 0.20/0.47        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.47        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['40', '58'])).
% 0.20/0.47  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.47  thf('60', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.20/0.47      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.47  thf(d1_xboole_0, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.47  thf('61', plain,
% 0.20/0.47      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.47  thf(t7_ordinal1, axiom,
% 0.20/0.47    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.47  thf('62', plain,
% 0.20/0.47      (![X12 : $i, X13 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X12 @ X13) | ~ (r1_tarski @ X13 @ X12))),
% 0.20/0.47      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.47  thf('63', plain,
% 0.20/0.47      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['61', '62'])).
% 0.20/0.47  thf('64', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.47      inference('sup-', [status(thm)], ['60', '63'])).
% 0.20/0.47  thf('65', plain,
% 0.20/0.47      (((v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.20/0.47      inference('demod', [status(thm)], ['59', '64'])).
% 0.20/0.47  thf('66', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('67', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 0.20/0.47      inference('clc', [status(thm)], ['65', '66'])).
% 0.20/0.47  thf('68', plain,
% 0.20/0.47      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.47      inference('sup+', [status(thm)], ['1', '67'])).
% 0.20/0.47  thf('69', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('70', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['68', '69'])).
% 0.20/0.47  thf(fc2_struct_0, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.47       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.47  thf('71', plain,
% 0.20/0.47      (![X16 : $i]:
% 0.20/0.47         (~ (v1_xboole_0 @ (u1_struct_0 @ X16))
% 0.20/0.47          | ~ (l1_struct_0 @ X16)
% 0.20/0.47          | (v2_struct_0 @ X16))),
% 0.20/0.47      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.47  thf('72', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['70', '71'])).
% 0.20/0.47  thf('73', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('74', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('demod', [status(thm)], ['72', '73'])).
% 0.20/0.47  thf('75', plain, ($false), inference('demod', [status(thm)], ['0', '74'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
