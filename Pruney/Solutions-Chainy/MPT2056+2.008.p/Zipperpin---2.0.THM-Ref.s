%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6LVkofiRJ0

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 237 expanded)
%              Number of leaves         :   47 (  99 expanded)
%              Depth                    :   20
%              Number of atoms          : 1016 (2544 expanded)
%              Number of equality atoms :   70 ( 158 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

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
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X15 ) @ X16 )
      | ( r2_hidden @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t1_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X20: $i] :
      ( ( X20 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X20 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t1_mcart_1])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X11: $i] :
      ( ( k2_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,(
    sk_B_2
 != ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('19',plain,(
    ! [X24: $i] :
      ( ( k3_yellow_1 @ X24 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('20',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

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

thf('21',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( v2_waybel_0 @ X26 @ ( k3_yellow_1 @ ( k2_struct_0 @ X27 ) ) )
      | ~ ( v13_waybel_0 @ X26 @ ( k3_yellow_1 @ ( k2_struct_0 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X27 ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X27 ) ) ) @ X26 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X27 @ ( k3_yellow19 @ X27 @ ( k2_struct_0 @ X27 ) @ X26 ) ) )
      | ~ ( l1_struct_0 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow19])).

thf('22',plain,(
    ! [X24: $i] :
      ( ( k3_yellow_1 @ X24 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('23',plain,(
    ! [X24: $i] :
      ( ( k3_yellow_1 @ X24 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('24',plain,(
    ! [X24: $i] :
      ( ( k3_yellow_1 @ X24 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf(t4_waybel_7,axiom,(
    ! [A: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ A ) )
      = ( k9_setfam_1 @ A ) ) )).

thf('25',plain,(
    ! [X25: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X25 ) )
      = ( k9_setfam_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t4_waybel_7])).

thf('26',plain,(
    ! [X24: $i] :
      ( ( k3_yellow_1 @ X24 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('27',plain,(
    ! [X25: $i] :
      ( ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X25 ) ) )
      = ( k9_setfam_1 @ X25 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('28',plain,(
    ! [X21: $i] :
      ( ( k9_setfam_1 @ X21 )
      = ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('29',plain,(
    ! [X24: $i] :
      ( ( k3_yellow_1 @ X24 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('30',plain,(
    ! [X25: $i] :
      ( ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X25 ) ) )
      = ( k9_setfam_1 @ X25 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('31',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( v2_waybel_0 @ X26 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X27 ) ) ) )
      | ~ ( v13_waybel_0 @ X26 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X27 ) ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ X27 ) ) ) )
      | ( ( k7_subset_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ X27 ) ) @ X26 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X27 @ ( k3_yellow19 @ X27 @ ( k2_struct_0 @ X27 ) @ X26 ) ) )
      | ~ ( l1_struct_0 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','27','28','29','30'])).

thf('32',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) @ sk_B_2 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
    | ~ ( m1_subset_1 @ sk_B_2 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['20','31'])).

thf('33',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X24: $i] :
      ( ( k3_yellow_1 @ X24 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('36',plain,(
    ! [X21: $i] :
      ( ( k9_setfam_1 @ X21 )
      = ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('37',plain,(
    m1_subset_1 @ sk_B_2 @ ( k9_setfam_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X25: $i] :
      ( ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X25 ) ) )
      = ( k9_setfam_1 @ X25 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('39',plain,(
    m1_subset_1 @ sk_B_2 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X24: $i] :
      ( ( k3_yellow_1 @ X24 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('42',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) @ sk_B_2 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['32','33','39','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B_2 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('45',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( ( k7_subset_1 @ X18 @ X17 @ X19 )
        = ( k4_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('46',plain,(
    ! [X21: $i] :
      ( ( k9_setfam_1 @ X21 )
      = ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('47',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k9_setfam_1 @ X18 ) )
      | ( ( k7_subset_1 @ X18 @ X17 @ X19 )
        = ( k4_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) @ sk_B_2 @ X0 )
      = ( k4_xboole_0 @ sk_B_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_xboole_0 @ sk_B_2 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['43','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( ( k4_xboole_0 @ sk_B_2 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( k4_xboole_0 @ sk_B_2 @ ( k1_tarski @ k1_xboole_0 ) )
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    sk_B_2
 != ( k4_xboole_0 @ sk_B_2 @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['17','53'])).

thf('55',plain,
    ( ( sk_B_2 != sk_B_2 )
    | ( r2_hidden @ k1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['16','54'])).

thf('56',plain,(
    r2_hidden @ k1_xboole_0 @ sk_B_2 ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    v2_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

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

thf('58',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( v1_subset_1 @ X28 @ ( u1_struct_0 @ ( k3_yellow_1 @ X29 ) ) )
      | ~ ( v2_waybel_0 @ X28 @ ( k3_yellow_1 @ X29 ) )
      | ~ ( v13_waybel_0 @ X28 @ ( k3_yellow_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X29 ) ) ) )
      | ~ ( r2_hidden @ X30 @ X28 )
      | ~ ( v1_xboole_0 @ X30 )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t2_yellow19])).

thf('59',plain,(
    ! [X24: $i] :
      ( ( k3_yellow_1 @ X24 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('60',plain,(
    ! [X25: $i] :
      ( ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X25 ) ) )
      = ( k9_setfam_1 @ X25 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('61',plain,(
    ! [X24: $i] :
      ( ( k3_yellow_1 @ X24 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('62',plain,(
    ! [X24: $i] :
      ( ( k3_yellow_1 @ X24 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('63',plain,(
    ! [X24: $i] :
      ( ( k3_yellow_1 @ X24 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('64',plain,(
    ! [X25: $i] :
      ( ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X25 ) ) )
      = ( k9_setfam_1 @ X25 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('65',plain,(
    ! [X21: $i] :
      ( ( k9_setfam_1 @ X21 )
      = ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('66',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( v1_subset_1 @ X28 @ ( k9_setfam_1 @ X29 ) )
      | ~ ( v2_waybel_0 @ X28 @ ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) )
      | ~ ( v13_waybel_0 @ X28 @ ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k9_setfam_1 @ ( k9_setfam_1 @ X29 ) ) )
      | ~ ( r2_hidden @ X30 @ X28 )
      | ~ ( v1_xboole_0 @ X30 )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(demod,[status(thm)],['58','59','60','61','62','63','64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( m1_subset_1 @ sk_B_2 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B_2 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['57','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_B_2 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('69',plain,(
    v13_waybel_0 @ sk_B_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('70',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X24: $i] :
      ( ( k3_yellow_1 @ X24 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('72',plain,(
    v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X25: $i] :
      ( ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X25 ) ) )
      = ( k9_setfam_1 @ X25 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('74',plain,(
    v1_subset_1 @ sk_B_2 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ( v1_xboole_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['67','68','69','74'])).

thf('76',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','75'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('77',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('78',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X20: $i] :
      ( ( X20 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X20 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t1_mcart_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('82',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k2_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','84'])).

thf('86',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['85','86'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('88',plain,(
    ! [X23: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('89',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('91',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,(
    $false ),
    inference(demod,[status(thm)],['0','92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6LVkofiRJ0
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:19:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 145 iterations in 0.061s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.21/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.52  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.21/0.52  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.21/0.52  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.21/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.52  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.52  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.21/0.52  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.21/0.52  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.52  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.21/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.52  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.21/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.52  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.21/0.52  thf(t15_yellow19, conjecture,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.52             ( v1_subset_1 @
% 0.21/0.52               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.21/0.52             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.52             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.52             ( m1_subset_1 @
% 0.21/0.52               B @ 
% 0.21/0.52               ( k1_zfmisc_1 @
% 0.21/0.52                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.21/0.52           ( ( B ) =
% 0.21/0.52             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i]:
% 0.21/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.52          ( ![B:$i]:
% 0.21/0.52            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.52                ( v1_subset_1 @
% 0.21/0.52                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.21/0.52                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.52                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.52                ( m1_subset_1 @
% 0.21/0.52                  B @ 
% 0.21/0.52                  ( k1_zfmisc_1 @
% 0.21/0.52                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.21/0.52              ( ( B ) =
% 0.21/0.52                ( k2_yellow19 @
% 0.21/0.52                  A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t15_yellow19])).
% 0.21/0.52  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(d3_struct_0, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      (![X22 : $i]:
% 0.21/0.52         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.52  thf(l27_zfmisc_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (![X15 : $i, X16 : $i]:
% 0.21/0.52         ((r1_xboole_0 @ (k1_tarski @ X15) @ X16) | (r2_hidden @ X15 @ X16))),
% 0.21/0.52      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.21/0.52  thf(t1_mcart_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.52          ( ![B:$i]: ( ~( ( r2_hidden @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) ) ))).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X20 : $i]:
% 0.21/0.52         (((X20) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X20) @ X20))),
% 0.21/0.52      inference('cnf', [status(esa)], [t1_mcart_1])).
% 0.21/0.52  thf(t4_xboole_0, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.52            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.52       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.52            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.21/0.52          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.21/0.52      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((r2_hidden @ X1 @ X0)
% 0.21/0.52          | ((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '5'])).
% 0.21/0.52  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.52    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.52  thf(t100_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X9 : $i, X10 : $i]:
% 0.21/0.52         ((k4_xboole_0 @ X9 @ X10)
% 0.21/0.52           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((k4_xboole_0 @ X0 @ X1)
% 0.21/0.52           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['7', '8'])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((k4_xboole_0 @ X0 @ (k1_tarski @ X1))
% 0.21/0.52            = (k5_xboole_0 @ X0 @ k1_xboole_0))
% 0.21/0.52          | (r2_hidden @ X1 @ X0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['6', '9'])).
% 0.21/0.52  thf(t4_boole, axiom,
% 0.21/0.52    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (![X12 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [t4_boole])).
% 0.21/0.52  thf(t98_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      (![X13 : $i, X14 : $i]:
% 0.21/0.52         ((k2_xboole_0 @ X13 @ X14)
% 0.21/0.52           = (k5_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.52  thf(t1_boole, axiom,
% 0.21/0.52    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.52  thf('14', plain, (![X11 : $i]: ((k2_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.21/0.52      inference('cnf', [status(esa)], [t1_boole])).
% 0.21/0.52  thf('15', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['13', '14'])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((k4_xboole_0 @ X0 @ (k1_tarski @ X1)) = (X0))
% 0.21/0.52          | (r2_hidden @ X1 @ X0))),
% 0.21/0.52      inference('demod', [status(thm)], ['10', '15'])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (((sk_B_2)
% 0.21/0.52         != (k2_yellow19 @ sk_A @ 
% 0.21/0.52             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      ((v2_waybel_0 @ sk_B_2 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(d2_yellow_1, axiom,
% 0.21/0.52    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (![X24 : $i]: ((k3_yellow_1 @ X24) = (k3_lattice3 @ (k1_lattice3 @ X24)))),
% 0.21/0.52      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      ((v2_waybel_0 @ sk_B_2 @ 
% 0.21/0.52        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.52      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.52  thf(t14_yellow19, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.52             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.52             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.52             ( m1_subset_1 @
% 0.21/0.52               B @ 
% 0.21/0.52               ( k1_zfmisc_1 @
% 0.21/0.52                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.21/0.52           ( ( k7_subset_1 @
% 0.21/0.52               ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ 
% 0.21/0.52               ( k1_tarski @ k1_xboole_0 ) ) =
% 0.21/0.52             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (![X26 : $i, X27 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ X26)
% 0.21/0.52          | ~ (v2_waybel_0 @ X26 @ (k3_yellow_1 @ (k2_struct_0 @ X27)))
% 0.21/0.52          | ~ (v13_waybel_0 @ X26 @ (k3_yellow_1 @ (k2_struct_0 @ X27)))
% 0.21/0.52          | ~ (m1_subset_1 @ X26 @ 
% 0.21/0.52               (k1_zfmisc_1 @ 
% 0.21/0.52                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X27)))))
% 0.21/0.52          | ((k7_subset_1 @ 
% 0.21/0.52              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X27))) @ X26 @ 
% 0.21/0.52              (k1_tarski @ k1_xboole_0))
% 0.21/0.52              = (k2_yellow19 @ X27 @ 
% 0.21/0.52                 (k3_yellow19 @ X27 @ (k2_struct_0 @ X27) @ X26)))
% 0.21/0.52          | ~ (l1_struct_0 @ X27)
% 0.21/0.52          | (v2_struct_0 @ X27))),
% 0.21/0.52      inference('cnf', [status(esa)], [t14_yellow19])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (![X24 : $i]: ((k3_yellow_1 @ X24) = (k3_lattice3 @ (k1_lattice3 @ X24)))),
% 0.21/0.52      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      (![X24 : $i]: ((k3_yellow_1 @ X24) = (k3_lattice3 @ (k1_lattice3 @ X24)))),
% 0.21/0.52      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      (![X24 : $i]: ((k3_yellow_1 @ X24) = (k3_lattice3 @ (k1_lattice3 @ X24)))),
% 0.21/0.52      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.52  thf(t4_waybel_7, axiom,
% 0.21/0.52    (![A:$i]: ( ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) = ( k9_setfam_1 @ A ) ))).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      (![X25 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X25)) = (k9_setfam_1 @ X25))),
% 0.21/0.52      inference('cnf', [status(esa)], [t4_waybel_7])).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      (![X24 : $i]: ((k3_yellow_1 @ X24) = (k3_lattice3 @ (k1_lattice3 @ X24)))),
% 0.21/0.52      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      (![X25 : $i]:
% 0.21/0.52         ((u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X25)))
% 0.21/0.52           = (k9_setfam_1 @ X25))),
% 0.21/0.52      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.52  thf(redefinition_k9_setfam_1, axiom,
% 0.21/0.52    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.52  thf('28', plain, (![X21 : $i]: ((k9_setfam_1 @ X21) = (k1_zfmisc_1 @ X21))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.21/0.52  thf('29', plain,
% 0.21/0.52      (![X24 : $i]: ((k3_yellow_1 @ X24) = (k3_lattice3 @ (k1_lattice3 @ X24)))),
% 0.21/0.52      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.52  thf('30', plain,
% 0.21/0.52      (![X25 : $i]:
% 0.21/0.52         ((u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X25)))
% 0.21/0.52           = (k9_setfam_1 @ X25))),
% 0.21/0.52      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.52  thf('31', plain,
% 0.21/0.52      (![X26 : $i, X27 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ X26)
% 0.21/0.52          | ~ (v2_waybel_0 @ X26 @ 
% 0.21/0.52               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X27))))
% 0.21/0.52          | ~ (v13_waybel_0 @ X26 @ 
% 0.21/0.52               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X27))))
% 0.21/0.52          | ~ (m1_subset_1 @ X26 @ 
% 0.21/0.52               (k9_setfam_1 @ (k9_setfam_1 @ (k2_struct_0 @ X27))))
% 0.21/0.52          | ((k7_subset_1 @ (k9_setfam_1 @ (k2_struct_0 @ X27)) @ X26 @ 
% 0.21/0.52              (k1_tarski @ k1_xboole_0))
% 0.21/0.52              = (k2_yellow19 @ X27 @ 
% 0.21/0.52                 (k3_yellow19 @ X27 @ (k2_struct_0 @ X27) @ X26)))
% 0.21/0.52          | ~ (l1_struct_0 @ X27)
% 0.21/0.52          | (v2_struct_0 @ X27))),
% 0.21/0.52      inference('demod', [status(thm)],
% 0.21/0.52                ['21', '22', '23', '24', '27', '28', '29', '30'])).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_A)
% 0.21/0.52        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.52        | ((k7_subset_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A)) @ sk_B_2 @ 
% 0.21/0.52            (k1_tarski @ k1_xboole_0))
% 0.21/0.52            = (k2_yellow19 @ sk_A @ 
% 0.21/0.52               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))
% 0.21/0.52        | ~ (m1_subset_1 @ sk_B_2 @ 
% 0.21/0.52             (k9_setfam_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A))))
% 0.21/0.52        | ~ (v13_waybel_0 @ sk_B_2 @ 
% 0.21/0.52             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.21/0.52        | (v1_xboole_0 @ sk_B_2))),
% 0.21/0.52      inference('sup-', [status(thm)], ['20', '31'])).
% 0.21/0.52  thf('33', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('34', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B_2 @ 
% 0.21/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('35', plain,
% 0.21/0.52      (![X24 : $i]: ((k3_yellow_1 @ X24) = (k3_lattice3 @ (k1_lattice3 @ X24)))),
% 0.21/0.52      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.52  thf('36', plain, (![X21 : $i]: ((k9_setfam_1 @ X21) = (k1_zfmisc_1 @ X21))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.21/0.52  thf('37', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B_2 @ 
% 0.21/0.52        (k9_setfam_1 @ 
% 0.21/0.52         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.21/0.52      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.21/0.52  thf('38', plain,
% 0.21/0.52      (![X25 : $i]:
% 0.21/0.52         ((u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X25)))
% 0.21/0.52           = (k9_setfam_1 @ X25))),
% 0.21/0.52      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.52  thf('39', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B_2 @ 
% 0.21/0.52        (k9_setfam_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.52      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.52  thf('40', plain,
% 0.21/0.52      ((v13_waybel_0 @ sk_B_2 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('41', plain,
% 0.21/0.52      (![X24 : $i]: ((k3_yellow_1 @ X24) = (k3_lattice3 @ (k1_lattice3 @ X24)))),
% 0.21/0.52      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.52  thf('42', plain,
% 0.21/0.52      ((v13_waybel_0 @ sk_B_2 @ 
% 0.21/0.52        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.52      inference('demod', [status(thm)], ['40', '41'])).
% 0.21/0.52  thf('43', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_A)
% 0.21/0.52        | ((k7_subset_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A)) @ sk_B_2 @ 
% 0.21/0.52            (k1_tarski @ k1_xboole_0))
% 0.21/0.52            = (k2_yellow19 @ sk_A @ 
% 0.21/0.52               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))
% 0.21/0.52        | (v1_xboole_0 @ sk_B_2))),
% 0.21/0.52      inference('demod', [status(thm)], ['32', '33', '39', '42'])).
% 0.21/0.52  thf('44', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B_2 @ 
% 0.21/0.52        (k9_setfam_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.52      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.52  thf(redefinition_k7_subset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.52       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.21/0.52  thf('45', plain,
% 0.21/0.52      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.21/0.52          | ((k7_subset_1 @ X18 @ X17 @ X19) = (k4_xboole_0 @ X17 @ X19)))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.21/0.52  thf('46', plain, (![X21 : $i]: ((k9_setfam_1 @ X21) = (k1_zfmisc_1 @ X21))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.21/0.52  thf('47', plain,
% 0.21/0.52      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X17 @ (k9_setfam_1 @ X18))
% 0.21/0.52          | ((k7_subset_1 @ X18 @ X17 @ X19) = (k4_xboole_0 @ X17 @ X19)))),
% 0.21/0.52      inference('demod', [status(thm)], ['45', '46'])).
% 0.21/0.52  thf('48', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((k7_subset_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A)) @ sk_B_2 @ X0)
% 0.21/0.52           = (k4_xboole_0 @ sk_B_2 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['44', '47'])).
% 0.21/0.52  thf('49', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_A)
% 0.21/0.52        | ((k4_xboole_0 @ sk_B_2 @ (k1_tarski @ k1_xboole_0))
% 0.21/0.52            = (k2_yellow19 @ sk_A @ 
% 0.21/0.52               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))
% 0.21/0.52        | (v1_xboole_0 @ sk_B_2))),
% 0.21/0.52      inference('demod', [status(thm)], ['43', '48'])).
% 0.21/0.52  thf('50', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('51', plain,
% 0.21/0.52      (((v1_xboole_0 @ sk_B_2)
% 0.21/0.52        | ((k4_xboole_0 @ sk_B_2 @ (k1_tarski @ k1_xboole_0))
% 0.21/0.52            = (k2_yellow19 @ sk_A @ 
% 0.21/0.52               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2))))),
% 0.21/0.52      inference('clc', [status(thm)], ['49', '50'])).
% 0.21/0.52  thf('52', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('53', plain,
% 0.21/0.52      (((k4_xboole_0 @ sk_B_2 @ (k1_tarski @ k1_xboole_0))
% 0.21/0.52         = (k2_yellow19 @ sk_A @ 
% 0.21/0.52            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_2)))),
% 0.21/0.52      inference('clc', [status(thm)], ['51', '52'])).
% 0.21/0.52  thf('54', plain,
% 0.21/0.52      (((sk_B_2) != (k4_xboole_0 @ sk_B_2 @ (k1_tarski @ k1_xboole_0)))),
% 0.21/0.52      inference('demod', [status(thm)], ['17', '53'])).
% 0.21/0.52  thf('55', plain,
% 0.21/0.52      ((((sk_B_2) != (sk_B_2)) | (r2_hidden @ k1_xboole_0 @ sk_B_2))),
% 0.21/0.52      inference('sup-', [status(thm)], ['16', '54'])).
% 0.21/0.52  thf('56', plain, ((r2_hidden @ k1_xboole_0 @ sk_B_2)),
% 0.21/0.52      inference('simplify', [status(thm)], ['55'])).
% 0.21/0.52  thf('57', plain,
% 0.21/0.52      ((v2_waybel_0 @ sk_B_2 @ 
% 0.21/0.52        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.52      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.52  thf(t2_yellow19, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.52             ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 0.21/0.52             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.21/0.52             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.21/0.52             ( m1_subset_1 @
% 0.21/0.52               B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 0.21/0.52           ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ))).
% 0.21/0.52  thf('58', plain,
% 0.21/0.52      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ X28)
% 0.21/0.52          | ~ (v1_subset_1 @ X28 @ (u1_struct_0 @ (k3_yellow_1 @ X29)))
% 0.21/0.52          | ~ (v2_waybel_0 @ X28 @ (k3_yellow_1 @ X29))
% 0.21/0.52          | ~ (v13_waybel_0 @ X28 @ (k3_yellow_1 @ X29))
% 0.21/0.52          | ~ (m1_subset_1 @ X28 @ 
% 0.21/0.52               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X29))))
% 0.21/0.52          | ~ (r2_hidden @ X30 @ X28)
% 0.21/0.52          | ~ (v1_xboole_0 @ X30)
% 0.21/0.52          | (v1_xboole_0 @ X29))),
% 0.21/0.52      inference('cnf', [status(esa)], [t2_yellow19])).
% 0.21/0.52  thf('59', plain,
% 0.21/0.52      (![X24 : $i]: ((k3_yellow_1 @ X24) = (k3_lattice3 @ (k1_lattice3 @ X24)))),
% 0.21/0.52      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.52  thf('60', plain,
% 0.21/0.52      (![X25 : $i]:
% 0.21/0.52         ((u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X25)))
% 0.21/0.52           = (k9_setfam_1 @ X25))),
% 0.21/0.52      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.52  thf('61', plain,
% 0.21/0.52      (![X24 : $i]: ((k3_yellow_1 @ X24) = (k3_lattice3 @ (k1_lattice3 @ X24)))),
% 0.21/0.52      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.52  thf('62', plain,
% 0.21/0.52      (![X24 : $i]: ((k3_yellow_1 @ X24) = (k3_lattice3 @ (k1_lattice3 @ X24)))),
% 0.21/0.52      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.52  thf('63', plain,
% 0.21/0.52      (![X24 : $i]: ((k3_yellow_1 @ X24) = (k3_lattice3 @ (k1_lattice3 @ X24)))),
% 0.21/0.52      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.52  thf('64', plain,
% 0.21/0.52      (![X25 : $i]:
% 0.21/0.52         ((u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X25)))
% 0.21/0.52           = (k9_setfam_1 @ X25))),
% 0.21/0.52      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.52  thf('65', plain, (![X21 : $i]: ((k9_setfam_1 @ X21) = (k1_zfmisc_1 @ X21))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.21/0.52  thf('66', plain,
% 0.21/0.52      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ X28)
% 0.21/0.52          | ~ (v1_subset_1 @ X28 @ (k9_setfam_1 @ X29))
% 0.21/0.52          | ~ (v2_waybel_0 @ X28 @ (k3_lattice3 @ (k1_lattice3 @ X29)))
% 0.21/0.52          | ~ (v13_waybel_0 @ X28 @ (k3_lattice3 @ (k1_lattice3 @ X29)))
% 0.21/0.52          | ~ (m1_subset_1 @ X28 @ (k9_setfam_1 @ (k9_setfam_1 @ X29)))
% 0.21/0.52          | ~ (r2_hidden @ X30 @ X28)
% 0.21/0.52          | ~ (v1_xboole_0 @ X30)
% 0.21/0.52          | (v1_xboole_0 @ X29))),
% 0.21/0.52      inference('demod', [status(thm)],
% 0.21/0.52                ['58', '59', '60', '61', '62', '63', '64', '65'])).
% 0.21/0.52  thf('67', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.52          | ~ (v1_xboole_0 @ X0)
% 0.21/0.52          | ~ (r2_hidden @ X0 @ sk_B_2)
% 0.21/0.52          | ~ (m1_subset_1 @ sk_B_2 @ 
% 0.21/0.52               (k9_setfam_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A))))
% 0.21/0.52          | ~ (v13_waybel_0 @ sk_B_2 @ 
% 0.21/0.52               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.21/0.52          | ~ (v1_subset_1 @ sk_B_2 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A)))
% 0.21/0.52          | (v1_xboole_0 @ sk_B_2))),
% 0.21/0.52      inference('sup-', [status(thm)], ['57', '66'])).
% 0.21/0.52  thf('68', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B_2 @ 
% 0.21/0.52        (k9_setfam_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.52      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.52  thf('69', plain,
% 0.21/0.52      ((v13_waybel_0 @ sk_B_2 @ 
% 0.21/0.52        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.52      inference('demod', [status(thm)], ['40', '41'])).
% 0.21/0.52  thf('70', plain,
% 0.21/0.52      ((v1_subset_1 @ sk_B_2 @ 
% 0.21/0.52        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('71', plain,
% 0.21/0.52      (![X24 : $i]: ((k3_yellow_1 @ X24) = (k3_lattice3 @ (k1_lattice3 @ X24)))),
% 0.21/0.52      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.52  thf('72', plain,
% 0.21/0.52      ((v1_subset_1 @ sk_B_2 @ 
% 0.21/0.52        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.21/0.52      inference('demod', [status(thm)], ['70', '71'])).
% 0.21/0.52  thf('73', plain,
% 0.21/0.52      (![X25 : $i]:
% 0.21/0.52         ((u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X25)))
% 0.21/0.52           = (k9_setfam_1 @ X25))),
% 0.21/0.52      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.52  thf('74', plain,
% 0.21/0.52      ((v1_subset_1 @ sk_B_2 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.52      inference('demod', [status(thm)], ['72', '73'])).
% 0.21/0.52  thf('75', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.52          | ~ (v1_xboole_0 @ X0)
% 0.21/0.52          | ~ (r2_hidden @ X0 @ sk_B_2)
% 0.21/0.52          | (v1_xboole_0 @ sk_B_2))),
% 0.21/0.52      inference('demod', [status(thm)], ['67', '68', '69', '74'])).
% 0.21/0.52  thf('76', plain,
% 0.21/0.52      (((v1_xboole_0 @ sk_B_2)
% 0.21/0.52        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.52        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['56', '75'])).
% 0.21/0.52  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.52  thf('77', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.52  thf('78', plain,
% 0.21/0.52      (((v1_xboole_0 @ sk_B_2) | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.52      inference('demod', [status(thm)], ['76', '77'])).
% 0.21/0.52  thf('79', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('80', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 0.21/0.52      inference('clc', [status(thm)], ['78', '79'])).
% 0.21/0.52  thf('81', plain,
% 0.21/0.52      (![X20 : $i]:
% 0.21/0.52         (((X20) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X20) @ X20))),
% 0.21/0.52      inference('cnf', [status(esa)], [t1_mcart_1])).
% 0.21/0.52  thf(d1_xboole_0, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.52  thf('82', plain,
% 0.21/0.52      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.21/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.52  thf('83', plain,
% 0.21/0.52      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['81', '82'])).
% 0.21/0.52  thf('84', plain, (((k2_struct_0 @ sk_A) = (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['80', '83'])).
% 0.21/0.52  thf('85', plain,
% 0.21/0.52      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)) | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup+', [status(thm)], ['1', '84'])).
% 0.21/0.52  thf('86', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('87', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 0.21/0.52      inference('demod', [status(thm)], ['85', '86'])).
% 0.21/0.52  thf(fc2_struct_0, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.52       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.52  thf('88', plain,
% 0.21/0.52      (![X23 : $i]:
% 0.21/0.52         (~ (v1_xboole_0 @ (u1_struct_0 @ X23))
% 0.21/0.52          | ~ (l1_struct_0 @ X23)
% 0.21/0.52          | (v2_struct_0 @ X23))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.52  thf('89', plain,
% 0.21/0.52      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.52        | (v2_struct_0 @ sk_A)
% 0.21/0.52        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['87', '88'])).
% 0.21/0.52  thf('90', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.52  thf('91', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('92', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('demod', [status(thm)], ['89', '90', '91'])).
% 0.21/0.52  thf('93', plain, ($false), inference('demod', [status(thm)], ['0', '92'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
