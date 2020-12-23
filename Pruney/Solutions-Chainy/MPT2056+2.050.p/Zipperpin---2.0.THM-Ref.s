%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YZK4PShjDe

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 152 expanded)
%              Number of leaves         :   34 (  65 expanded)
%              Depth                    :   16
%              Number of atoms          :  784 (2022 expanded)
%              Number of equality atoms :   31 (  78 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

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

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X7 ) @ X8 )
      | ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    sk_B
 != ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('13',plain,(
    ! [X13: $i] :
      ( ( k3_yellow_1 @ X13 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

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

thf('15',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v1_xboole_0 @ X14 )
      | ~ ( v2_waybel_0 @ X14 @ ( k3_yellow_1 @ ( k2_struct_0 @ X15 ) ) )
      | ~ ( v13_waybel_0 @ X14 @ ( k3_yellow_1 @ ( k2_struct_0 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X15 ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X15 ) ) ) @ X14 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X15 @ ( k3_yellow19 @ X15 @ ( k2_struct_0 @ X15 ) @ X14 ) ) )
      | ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow19])).

thf('16',plain,(
    ! [X13: $i] :
      ( ( k3_yellow_1 @ X13 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('17',plain,(
    ! [X13: $i] :
      ( ( k3_yellow_1 @ X13 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('18',plain,(
    ! [X13: $i] :
      ( ( k3_yellow_1 @ X13 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('19',plain,(
    ! [X13: $i] :
      ( ( k3_yellow_1 @ X13 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('20',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v1_xboole_0 @ X14 )
      | ~ ( v2_waybel_0 @ X14 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X15 ) ) ) )
      | ~ ( v13_waybel_0 @ X14 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X15 ) ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X15 ) ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X15 ) ) ) ) @ X14 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X15 @ ( k3_yellow19 @ X15 @ ( k2_struct_0 @ X15 ) @ X14 ) ) )
      | ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( ( k7_subset_1 @ X10 @ X9 @ X11 )
        = ( k4_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X13: $i] :
      ( ( k3_yellow_1 @ X13 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('28',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X13: $i] :
      ( ( k3_yellow_1 @ X13 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('31',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['21','22','25','28','31'])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    sk_B
 != ( k4_xboole_0 @ sk_B @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['11','36'])).

thf('38',plain,
    ( ( sk_B != sk_B )
    | ( r2_hidden @ k1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['10','37'])).

thf('39',plain,(
    r2_hidden @ k1_xboole_0 @ sk_B ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

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

thf('41',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ~ ( v1_subset_1 @ X16 @ ( u1_struct_0 @ ( k3_yellow_1 @ X17 ) ) )
      | ~ ( v2_waybel_0 @ X16 @ ( k3_yellow_1 @ X17 ) )
      | ~ ( v13_waybel_0 @ X16 @ ( k3_yellow_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X17 ) ) ) )
      | ~ ( r2_hidden @ X18 @ X16 )
      | ~ ( v1_xboole_0 @ X18 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t2_yellow19])).

thf('42',plain,(
    ! [X13: $i] :
      ( ( k3_yellow_1 @ X13 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('43',plain,(
    ! [X13: $i] :
      ( ( k3_yellow_1 @ X13 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('44',plain,(
    ! [X13: $i] :
      ( ( k3_yellow_1 @ X13 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('45',plain,(
    ! [X13: $i] :
      ( ( k3_yellow_1 @ X13 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('46',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ~ ( v1_subset_1 @ X16 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) )
      | ~ ( v2_waybel_0 @ X16 @ ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) )
      | ~ ( v13_waybel_0 @ X16 @ ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ) )
      | ~ ( r2_hidden @ X18 @ X16 )
      | ~ ( v1_xboole_0 @ X18 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(demod,[status(thm)],['41','42','43','44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','46'])).

thf('48',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('49',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('50',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X13: $i] :
      ( ( k3_yellow_1 @ X13 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('52',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','48','49','52'])).

thf('54',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','53'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('55',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('56',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['56','57'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('59',plain,(
    ! [X12: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    $false ),
    inference(demod,[status(thm)],['0','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YZK4PShjDe
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:01:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 42 iterations in 0.023s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.48  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.21/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.21/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.48  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.21/0.48  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.21/0.48  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.21/0.48  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.48  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.21/0.48  thf(t15_yellow19, conjecture,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.48             ( v1_subset_1 @
% 0.21/0.48               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.21/0.48             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.48             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.48             ( m1_subset_1 @
% 0.21/0.48               B @ 
% 0.21/0.48               ( k1_zfmisc_1 @
% 0.21/0.48                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.21/0.48           ( ( B ) =
% 0.21/0.48             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]:
% 0.21/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.48          ( ![B:$i]:
% 0.21/0.48            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.48                ( v1_subset_1 @
% 0.21/0.48                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.21/0.48                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.48                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.48                ( m1_subset_1 @
% 0.21/0.48                  B @ 
% 0.21/0.48                  ( k1_zfmisc_1 @
% 0.21/0.48                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.21/0.48              ( ( B ) =
% 0.21/0.48                ( k2_yellow19 @
% 0.21/0.48                  A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t15_yellow19])).
% 0.21/0.48  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(l27_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ (k1_tarski @ X7) @ X8) | (r2_hidden @ X7 @ X8))),
% 0.21/0.48      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.21/0.48  thf(t3_xboole_0, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.21/0.48            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.48       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.48            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.21/0.48      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X2 @ X0)
% 0.21/0.48          | ~ (r2_hidden @ X2 @ X3)
% 0.21/0.48          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.21/0.48      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ X1 @ X0)
% 0.21/0.48          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.21/0.48          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.21/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ X0 @ X1)
% 0.21/0.48          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.21/0.48          | (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['2', '5'])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.48      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '7'])).
% 0.21/0.48  thf(t83_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X4 : $i, X5 : $i]:
% 0.21/0.48         (((k4_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r2_hidden @ X0 @ X1)
% 0.21/0.48          | ((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (((sk_B)
% 0.21/0.48         != (k2_yellow19 @ sk_A @ 
% 0.21/0.48             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_B @ 
% 0.21/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(d2_yellow_1, axiom,
% 0.21/0.48    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (![X13 : $i]: ((k3_yellow_1 @ X13) = (k3_lattice3 @ (k1_lattice3 @ X13)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_B @ 
% 0.21/0.48        (k1_zfmisc_1 @ 
% 0.21/0.48         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.21/0.48      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.48  thf(t14_yellow19, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.48             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.48             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.48             ( m1_subset_1 @
% 0.21/0.48               B @ 
% 0.21/0.48               ( k1_zfmisc_1 @
% 0.21/0.48                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.21/0.48           ( ( k7_subset_1 @
% 0.21/0.48               ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ 
% 0.21/0.48               ( k1_tarski @ k1_xboole_0 ) ) =
% 0.21/0.48             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (![X14 : $i, X15 : $i]:
% 0.21/0.48         ((v1_xboole_0 @ X14)
% 0.21/0.48          | ~ (v2_waybel_0 @ X14 @ (k3_yellow_1 @ (k2_struct_0 @ X15)))
% 0.21/0.48          | ~ (v13_waybel_0 @ X14 @ (k3_yellow_1 @ (k2_struct_0 @ X15)))
% 0.21/0.48          | ~ (m1_subset_1 @ X14 @ 
% 0.21/0.48               (k1_zfmisc_1 @ 
% 0.21/0.48                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X15)))))
% 0.21/0.48          | ((k7_subset_1 @ 
% 0.21/0.48              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X15))) @ X14 @ 
% 0.21/0.48              (k1_tarski @ k1_xboole_0))
% 0.21/0.48              = (k2_yellow19 @ X15 @ 
% 0.21/0.48                 (k3_yellow19 @ X15 @ (k2_struct_0 @ X15) @ X14)))
% 0.21/0.48          | ~ (l1_struct_0 @ X15)
% 0.21/0.48          | (v2_struct_0 @ X15))),
% 0.21/0.48      inference('cnf', [status(esa)], [t14_yellow19])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      (![X13 : $i]: ((k3_yellow_1 @ X13) = (k3_lattice3 @ (k1_lattice3 @ X13)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      (![X13 : $i]: ((k3_yellow_1 @ X13) = (k3_lattice3 @ (k1_lattice3 @ X13)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (![X13 : $i]: ((k3_yellow_1 @ X13) = (k3_lattice3 @ (k1_lattice3 @ X13)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (![X13 : $i]: ((k3_yellow_1 @ X13) = (k3_lattice3 @ (k1_lattice3 @ X13)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      (![X14 : $i, X15 : $i]:
% 0.21/0.48         ((v1_xboole_0 @ X14)
% 0.21/0.48          | ~ (v2_waybel_0 @ X14 @ 
% 0.21/0.48               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X15))))
% 0.21/0.48          | ~ (v13_waybel_0 @ X14 @ 
% 0.21/0.48               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X15))))
% 0.21/0.48          | ~ (m1_subset_1 @ X14 @ 
% 0.21/0.48               (k1_zfmisc_1 @ 
% 0.21/0.48                (u1_struct_0 @ 
% 0.21/0.48                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X15))))))
% 0.21/0.48          | ((k7_subset_1 @ 
% 0.21/0.48              (u1_struct_0 @ 
% 0.21/0.48               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X15)))) @ 
% 0.21/0.48              X14 @ (k1_tarski @ k1_xboole_0))
% 0.21/0.48              = (k2_yellow19 @ X15 @ 
% 0.21/0.48                 (k3_yellow19 @ X15 @ (k2_struct_0 @ X15) @ X14)))
% 0.21/0.48          | ~ (l1_struct_0 @ X15)
% 0.21/0.48          | (v2_struct_0 @ X15))),
% 0.21/0.48      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_A)
% 0.21/0.48        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.48        | ((k7_subset_1 @ 
% 0.21/0.48            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.21/0.48            sk_B @ (k1_tarski @ k1_xboole_0))
% 0.21/0.48            = (k2_yellow19 @ sk_A @ 
% 0.21/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.21/0.48        | ~ (v13_waybel_0 @ sk_B @ 
% 0.21/0.48             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.21/0.48        | ~ (v2_waybel_0 @ sk_B @ 
% 0.21/0.48             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.21/0.48        | (v1_xboole_0 @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['14', '20'])).
% 0.21/0.48  thf('22', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_B @ 
% 0.21/0.48        (k1_zfmisc_1 @ 
% 0.21/0.48         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.21/0.48      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.48  thf(redefinition_k7_subset_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.48       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.21/0.48          | ((k7_subset_1 @ X10 @ X9 @ X11) = (k4_xboole_0 @ X9 @ X11)))),
% 0.21/0.48      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((k7_subset_1 @ 
% 0.21/0.48           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.21/0.48           sk_B @ X0) = (k4_xboole_0 @ sk_B @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      ((v13_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      (![X13 : $i]: ((k3_yellow_1 @ X13) = (k3_lattice3 @ (k1_lattice3 @ X13)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      ((v13_waybel_0 @ sk_B @ 
% 0.21/0.48        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.48      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      ((v2_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('30', plain,
% 0.21/0.48      (![X13 : $i]: ((k3_yellow_1 @ X13) = (k3_lattice3 @ (k1_lattice3 @ X13)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.48  thf('31', plain,
% 0.21/0.48      ((v2_waybel_0 @ sk_B @ 
% 0.21/0.48        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.48      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.48  thf('32', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_A)
% 0.21/0.48        | ((k4_xboole_0 @ sk_B @ (k1_tarski @ k1_xboole_0))
% 0.21/0.48            = (k2_yellow19 @ sk_A @ 
% 0.21/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.21/0.48        | (v1_xboole_0 @ sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['21', '22', '25', '28', '31'])).
% 0.21/0.48  thf('33', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('34', plain,
% 0.21/0.48      (((v1_xboole_0 @ sk_B)
% 0.21/0.48        | ((k4_xboole_0 @ sk_B @ (k1_tarski @ k1_xboole_0))
% 0.21/0.48            = (k2_yellow19 @ sk_A @ 
% 0.21/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.21/0.48      inference('clc', [status(thm)], ['32', '33'])).
% 0.21/0.48  thf('35', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('36', plain,
% 0.21/0.48      (((k4_xboole_0 @ sk_B @ (k1_tarski @ k1_xboole_0))
% 0.21/0.48         = (k2_yellow19 @ sk_A @ 
% 0.21/0.48            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.21/0.48      inference('clc', [status(thm)], ['34', '35'])).
% 0.21/0.48  thf('37', plain,
% 0.21/0.48      (((sk_B) != (k4_xboole_0 @ sk_B @ (k1_tarski @ k1_xboole_0)))),
% 0.21/0.48      inference('demod', [status(thm)], ['11', '36'])).
% 0.21/0.48  thf('38', plain, ((((sk_B) != (sk_B)) | (r2_hidden @ k1_xboole_0 @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['10', '37'])).
% 0.21/0.48  thf('39', plain, ((r2_hidden @ k1_xboole_0 @ sk_B)),
% 0.21/0.48      inference('simplify', [status(thm)], ['38'])).
% 0.21/0.48  thf('40', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_B @ 
% 0.21/0.48        (k1_zfmisc_1 @ 
% 0.21/0.48         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.21/0.48      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.48  thf(t2_yellow19, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.48             ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 0.21/0.48             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.21/0.48             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.21/0.48             ( m1_subset_1 @
% 0.21/0.48               B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 0.21/0.48           ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ))).
% 0.21/0.48  thf('41', plain,
% 0.21/0.48      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.48         ((v1_xboole_0 @ X16)
% 0.21/0.48          | ~ (v1_subset_1 @ X16 @ (u1_struct_0 @ (k3_yellow_1 @ X17)))
% 0.21/0.48          | ~ (v2_waybel_0 @ X16 @ (k3_yellow_1 @ X17))
% 0.21/0.48          | ~ (v13_waybel_0 @ X16 @ (k3_yellow_1 @ X17))
% 0.21/0.48          | ~ (m1_subset_1 @ X16 @ 
% 0.21/0.48               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X17))))
% 0.21/0.48          | ~ (r2_hidden @ X18 @ X16)
% 0.21/0.48          | ~ (v1_xboole_0 @ X18)
% 0.21/0.48          | (v1_xboole_0 @ X17))),
% 0.21/0.48      inference('cnf', [status(esa)], [t2_yellow19])).
% 0.21/0.48  thf('42', plain,
% 0.21/0.48      (![X13 : $i]: ((k3_yellow_1 @ X13) = (k3_lattice3 @ (k1_lattice3 @ X13)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.48  thf('43', plain,
% 0.21/0.48      (![X13 : $i]: ((k3_yellow_1 @ X13) = (k3_lattice3 @ (k1_lattice3 @ X13)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.48  thf('44', plain,
% 0.21/0.48      (![X13 : $i]: ((k3_yellow_1 @ X13) = (k3_lattice3 @ (k1_lattice3 @ X13)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.48  thf('45', plain,
% 0.21/0.48      (![X13 : $i]: ((k3_yellow_1 @ X13) = (k3_lattice3 @ (k1_lattice3 @ X13)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.48  thf('46', plain,
% 0.21/0.48      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.48         ((v1_xboole_0 @ X16)
% 0.21/0.48          | ~ (v1_subset_1 @ X16 @ 
% 0.21/0.48               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X17))))
% 0.21/0.48          | ~ (v2_waybel_0 @ X16 @ (k3_lattice3 @ (k1_lattice3 @ X17)))
% 0.21/0.48          | ~ (v13_waybel_0 @ X16 @ (k3_lattice3 @ (k1_lattice3 @ X17)))
% 0.21/0.48          | ~ (m1_subset_1 @ X16 @ 
% 0.21/0.48               (k1_zfmisc_1 @ 
% 0.21/0.48                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X17)))))
% 0.21/0.48          | ~ (r2_hidden @ X18 @ X16)
% 0.21/0.48          | ~ (v1_xboole_0 @ X18)
% 0.21/0.48          | (v1_xboole_0 @ X17))),
% 0.21/0.48      inference('demod', [status(thm)], ['41', '42', '43', '44', '45'])).
% 0.21/0.48  thf('47', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.48          | ~ (v1_xboole_0 @ X0)
% 0.21/0.48          | ~ (r2_hidden @ X0 @ sk_B)
% 0.21/0.48          | ~ (v13_waybel_0 @ sk_B @ 
% 0.21/0.48               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.21/0.48          | ~ (v2_waybel_0 @ sk_B @ 
% 0.21/0.48               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.21/0.48          | ~ (v1_subset_1 @ sk_B @ 
% 0.21/0.48               (u1_struct_0 @ 
% 0.21/0.48                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.21/0.48          | (v1_xboole_0 @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['40', '46'])).
% 0.21/0.48  thf('48', plain,
% 0.21/0.48      ((v13_waybel_0 @ sk_B @ 
% 0.21/0.48        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.48      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.48  thf('49', plain,
% 0.21/0.48      ((v2_waybel_0 @ sk_B @ 
% 0.21/0.48        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.48      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.48  thf('50', plain,
% 0.21/0.48      ((v1_subset_1 @ sk_B @ 
% 0.21/0.48        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('51', plain,
% 0.21/0.48      (![X13 : $i]: ((k3_yellow_1 @ X13) = (k3_lattice3 @ (k1_lattice3 @ X13)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.48  thf('52', plain,
% 0.21/0.48      ((v1_subset_1 @ sk_B @ 
% 0.21/0.48        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.21/0.48      inference('demod', [status(thm)], ['50', '51'])).
% 0.21/0.48  thf('53', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.48          | ~ (v1_xboole_0 @ X0)
% 0.21/0.48          | ~ (r2_hidden @ X0 @ sk_B)
% 0.21/0.48          | (v1_xboole_0 @ sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['47', '48', '49', '52'])).
% 0.21/0.48  thf('54', plain,
% 0.21/0.48      (((v1_xboole_0 @ sk_B)
% 0.21/0.48        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.48        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['39', '53'])).
% 0.21/0.48  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.48  thf('55', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.48      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.48  thf('56', plain,
% 0.21/0.48      (((v1_xboole_0 @ sk_B) | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.48      inference('demod', [status(thm)], ['54', '55'])).
% 0.21/0.48  thf('57', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('58', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 0.21/0.48      inference('clc', [status(thm)], ['56', '57'])).
% 0.21/0.48  thf(fc5_struct_0, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.48       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.21/0.48  thf('59', plain,
% 0.21/0.48      (![X12 : $i]:
% 0.21/0.48         (~ (v1_xboole_0 @ (k2_struct_0 @ X12))
% 0.21/0.48          | ~ (l1_struct_0 @ X12)
% 0.21/0.48          | (v2_struct_0 @ X12))),
% 0.21/0.48      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.21/0.48  thf('60', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['58', '59'])).
% 0.21/0.48  thf('61', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('62', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('demod', [status(thm)], ['60', '61'])).
% 0.21/0.48  thf('63', plain, ($false), inference('demod', [status(thm)], ['0', '62'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
