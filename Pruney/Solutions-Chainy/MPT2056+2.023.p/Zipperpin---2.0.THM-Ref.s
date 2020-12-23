%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GTYPS6vGk6

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:43 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 173 expanded)
%              Number of leaves         :   38 (  72 expanded)
%              Depth                    :   17
%              Number of atoms          :  930 (2206 expanded)
%              Number of equality atoms :   42 (  89 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X10: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X12 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

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

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('6',plain,(
    ! [X24: $i,X25: $i,X27: $i] :
      ( ( r2_hidden @ X24 @ ( k4_xboole_0 @ X25 @ ( k1_tarski @ X27 ) ) )
      | ( X24 = X27 )
      | ~ ( r2_hidden @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( ( sk_C @ X1 @ X0 )
        = X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ X2 @ X1 )
        = X0 )
      | ( r1_xboole_0 @ X1 @ X2 )
      | ~ ( v1_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('11',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('17',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('18',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('23',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k4_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    sk_B_1
 != ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('27',plain,(
    ! [X32: $i] :
      ( ( k3_yellow_1 @ X32 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('28',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

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

thf('29',plain,(
    ! [X33: $i,X34: $i] :
      ( ( v1_xboole_0 @ X33 )
      | ~ ( v2_waybel_0 @ X33 @ ( k3_yellow_1 @ ( k2_struct_0 @ X34 ) ) )
      | ~ ( v13_waybel_0 @ X33 @ ( k3_yellow_1 @ ( k2_struct_0 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X34 ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X34 ) ) ) @ X33 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X34 @ ( k3_yellow19 @ X34 @ ( k2_struct_0 @ X34 ) @ X33 ) ) )
      | ~ ( l1_struct_0 @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow19])).

thf('30',plain,(
    ! [X32: $i] :
      ( ( k3_yellow_1 @ X32 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('31',plain,(
    ! [X32: $i] :
      ( ( k3_yellow_1 @ X32 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('32',plain,(
    ! [X32: $i] :
      ( ( k3_yellow_1 @ X32 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('33',plain,(
    ! [X32: $i] :
      ( ( k3_yellow_1 @ X32 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('34',plain,(
    ! [X33: $i,X34: $i] :
      ( ( v1_xboole_0 @ X33 )
      | ~ ( v2_waybel_0 @ X33 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X34 ) ) ) )
      | ~ ( v13_waybel_0 @ X33 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X34 ) ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X34 ) ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X34 ) ) ) ) @ X33 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X34 @ ( k3_yellow19 @ X34 @ ( k2_struct_0 @ X34 ) @ X33 ) ) )
      | ~ ( l1_struct_0 @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(demod,[status(thm)],['29','30','31','32','33'])).

thf('35',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['28','34'])).

thf('36',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('38',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ( ( k7_subset_1 @ X29 @ X28 @ X30 )
        = ( k4_xboole_0 @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_1 @ X0 )
      = ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X32: $i] :
      ( ( k3_yellow_1 @ X32 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('42',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X32: $i] :
      ( ( k3_yellow_1 @ X32 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('45',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['35','36','39','42','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    sk_B_1
 != ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['25','50'])).

thf('52',plain,
    ( ( sk_B_1 != sk_B_1 )
    | ( r2_hidden @ k1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['24','51'])).

thf('53',plain,(
    r2_hidden @ k1_xboole_0 @ sk_B_1 ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

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

thf('55',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( v1_xboole_0 @ X35 )
      | ~ ( v1_subset_1 @ X35 @ ( u1_struct_0 @ ( k3_yellow_1 @ X36 ) ) )
      | ~ ( v2_waybel_0 @ X35 @ ( k3_yellow_1 @ X36 ) )
      | ~ ( v13_waybel_0 @ X35 @ ( k3_yellow_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X36 ) ) ) )
      | ~ ( r2_hidden @ X37 @ X35 )
      | ~ ( v1_xboole_0 @ X37 )
      | ( v1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t2_yellow19])).

thf('56',plain,(
    ! [X32: $i] :
      ( ( k3_yellow_1 @ X32 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('57',plain,(
    ! [X32: $i] :
      ( ( k3_yellow_1 @ X32 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('58',plain,(
    ! [X32: $i] :
      ( ( k3_yellow_1 @ X32 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('59',plain,(
    ! [X32: $i] :
      ( ( k3_yellow_1 @ X32 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('60',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( v1_xboole_0 @ X35 )
      | ~ ( v1_subset_1 @ X35 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X36 ) ) ) )
      | ~ ( v2_waybel_0 @ X35 @ ( k3_lattice3 @ ( k1_lattice3 @ X36 ) ) )
      | ~ ( v13_waybel_0 @ X35 @ ( k3_lattice3 @ ( k1_lattice3 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X36 ) ) ) ) )
      | ~ ( r2_hidden @ X37 @ X35 )
      | ~ ( v1_xboole_0 @ X37 )
      | ( v1_xboole_0 @ X36 ) ) ),
    inference(demod,[status(thm)],['55','56','57','58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['54','60'])).

thf('62',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('63',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('64',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X32: $i] :
      ( ( k3_yellow_1 @ X32 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('66',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['61','62','63','66'])).

thf('68',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','67'])).

thf('69',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('70',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['70','71'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('73',plain,(
    ! [X31: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    $false ),
    inference(demod,[status(thm)],['0','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GTYPS6vGk6
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:08:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.51/1.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.51/1.74  % Solved by: fo/fo7.sh
% 1.51/1.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.51/1.74  % done 3838 iterations in 1.318s
% 1.51/1.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.51/1.74  % SZS output start Refutation
% 1.51/1.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.51/1.74  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 1.51/1.74  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.51/1.74  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 1.51/1.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.51/1.74  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 1.51/1.74  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.51/1.74  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.51/1.74  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.51/1.74  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.51/1.74  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.51/1.74  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 1.51/1.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.51/1.74  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.51/1.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.51/1.74  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 1.51/1.74  thf(sk_A_type, type, sk_A: $i).
% 1.51/1.74  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.51/1.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.51/1.74  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 1.51/1.74  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 1.51/1.74  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.51/1.74  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.51/1.74  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 1.51/1.74  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.51/1.74  thf(t15_yellow19, conjecture,
% 1.51/1.74    (![A:$i]:
% 1.51/1.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.51/1.74       ( ![B:$i]:
% 1.51/1.74         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 1.51/1.74             ( v1_subset_1 @
% 1.51/1.74               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 1.51/1.74             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 1.51/1.74             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 1.51/1.74             ( m1_subset_1 @
% 1.51/1.74               B @ 
% 1.51/1.74               ( k1_zfmisc_1 @
% 1.51/1.74                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 1.51/1.74           ( ( B ) =
% 1.51/1.74             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 1.51/1.74  thf(zf_stmt_0, negated_conjecture,
% 1.51/1.74    (~( ![A:$i]:
% 1.51/1.74        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.51/1.74          ( ![B:$i]:
% 1.51/1.74            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 1.51/1.74                ( v1_subset_1 @
% 1.51/1.74                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 1.51/1.74                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 1.51/1.74                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 1.51/1.74                ( m1_subset_1 @
% 1.51/1.74                  B @ 
% 1.51/1.74                  ( k1_zfmisc_1 @
% 1.51/1.74                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 1.51/1.74              ( ( B ) =
% 1.51/1.74                ( k2_yellow19 @
% 1.51/1.74                  A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) )),
% 1.51/1.74    inference('cnf.neg', [status(esa)], [t15_yellow19])).
% 1.51/1.74  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 1.51/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.74  thf(d10_xboole_0, axiom,
% 1.51/1.74    (![A:$i,B:$i]:
% 1.51/1.74     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.51/1.74  thf('1', plain,
% 1.51/1.74      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 1.51/1.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.51/1.74  thf('2', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 1.51/1.74      inference('simplify', [status(thm)], ['1'])).
% 1.51/1.74  thf(l32_xboole_1, axiom,
% 1.51/1.74    (![A:$i,B:$i]:
% 1.51/1.74     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.51/1.74  thf('3', plain,
% 1.51/1.74      (![X10 : $i, X12 : $i]:
% 1.51/1.74         (((k4_xboole_0 @ X10 @ X12) = (k1_xboole_0))
% 1.51/1.74          | ~ (r1_tarski @ X10 @ X12))),
% 1.51/1.74      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.51/1.74  thf('4', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.51/1.74      inference('sup-', [status(thm)], ['2', '3'])).
% 1.51/1.74  thf(t3_xboole_0, axiom,
% 1.51/1.74    (![A:$i,B:$i]:
% 1.51/1.74     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.51/1.74            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.51/1.74       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.51/1.74            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.51/1.74  thf('5', plain,
% 1.51/1.74      (![X3 : $i, X4 : $i]:
% 1.51/1.74         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 1.51/1.74      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.51/1.74  thf(t64_zfmisc_1, axiom,
% 1.51/1.74    (![A:$i,B:$i,C:$i]:
% 1.51/1.74     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 1.51/1.74       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 1.51/1.74  thf('6', plain,
% 1.51/1.74      (![X24 : $i, X25 : $i, X27 : $i]:
% 1.51/1.74         ((r2_hidden @ X24 @ (k4_xboole_0 @ X25 @ (k1_tarski @ X27)))
% 1.51/1.74          | ((X24) = (X27))
% 1.51/1.74          | ~ (r2_hidden @ X24 @ X25))),
% 1.51/1.74      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 1.51/1.74  thf('7', plain,
% 1.51/1.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.74         ((r1_xboole_0 @ X0 @ X1)
% 1.51/1.74          | ((sk_C @ X1 @ X0) = (X2))
% 1.51/1.74          | (r2_hidden @ (sk_C @ X1 @ X0) @ 
% 1.51/1.74             (k4_xboole_0 @ X0 @ (k1_tarski @ X2))))),
% 1.51/1.74      inference('sup-', [status(thm)], ['5', '6'])).
% 1.51/1.74  thf(d1_xboole_0, axiom,
% 1.51/1.74    (![A:$i]:
% 1.51/1.74     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.51/1.74  thf('8', plain,
% 1.51/1.74      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.51/1.74      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.51/1.74  thf('9', plain,
% 1.51/1.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.74         (((sk_C @ X2 @ X1) = (X0))
% 1.51/1.74          | (r1_xboole_0 @ X1 @ X2)
% 1.51/1.74          | ~ (v1_xboole_0 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 1.51/1.74      inference('sup-', [status(thm)], ['7', '8'])).
% 1.51/1.74  thf('10', plain,
% 1.51/1.74      (![X0 : $i, X1 : $i]:
% 1.51/1.74         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.51/1.74          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 1.51/1.74          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 1.51/1.74      inference('sup-', [status(thm)], ['4', '9'])).
% 1.51/1.74  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.51/1.74  thf('11', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.51/1.74      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.51/1.74  thf('12', plain,
% 1.51/1.74      (![X0 : $i, X1 : $i]:
% 1.51/1.74         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 1.51/1.74          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 1.51/1.74      inference('demod', [status(thm)], ['10', '11'])).
% 1.51/1.74  thf('13', plain,
% 1.51/1.74      (![X3 : $i, X4 : $i]:
% 1.51/1.74         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 1.51/1.74      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.51/1.74  thf('14', plain,
% 1.51/1.74      (![X0 : $i, X1 : $i]:
% 1.51/1.74         ((r2_hidden @ X0 @ X1)
% 1.51/1.74          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 1.51/1.74          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 1.51/1.74      inference('sup+', [status(thm)], ['12', '13'])).
% 1.51/1.74  thf('15', plain,
% 1.51/1.74      (![X0 : $i, X1 : $i]:
% 1.51/1.74         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 1.51/1.74      inference('simplify', [status(thm)], ['14'])).
% 1.51/1.74  thf('16', plain,
% 1.51/1.74      (![X3 : $i, X4 : $i]:
% 1.51/1.74         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 1.51/1.74      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.51/1.74  thf('17', plain,
% 1.51/1.74      (![X3 : $i, X4 : $i]:
% 1.51/1.74         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 1.51/1.74      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.51/1.74  thf('18', plain,
% 1.51/1.74      (![X3 : $i, X5 : $i, X6 : $i]:
% 1.51/1.74         (~ (r2_hidden @ X5 @ X3)
% 1.51/1.74          | ~ (r2_hidden @ X5 @ X6)
% 1.51/1.74          | ~ (r1_xboole_0 @ X3 @ X6))),
% 1.51/1.74      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.51/1.74  thf('19', plain,
% 1.51/1.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.74         ((r1_xboole_0 @ X1 @ X0)
% 1.51/1.74          | ~ (r1_xboole_0 @ X0 @ X2)
% 1.51/1.74          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 1.51/1.74      inference('sup-', [status(thm)], ['17', '18'])).
% 1.51/1.74  thf('20', plain,
% 1.51/1.74      (![X0 : $i, X1 : $i]:
% 1.51/1.74         ((r1_xboole_0 @ X0 @ X1)
% 1.51/1.74          | ~ (r1_xboole_0 @ X1 @ X0)
% 1.51/1.74          | (r1_xboole_0 @ X0 @ X1))),
% 1.51/1.74      inference('sup-', [status(thm)], ['16', '19'])).
% 1.51/1.74  thf('21', plain,
% 1.51/1.74      (![X0 : $i, X1 : $i]:
% 1.51/1.74         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 1.51/1.74      inference('simplify', [status(thm)], ['20'])).
% 1.51/1.74  thf('22', plain,
% 1.51/1.74      (![X0 : $i, X1 : $i]:
% 1.51/1.74         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 1.51/1.74      inference('sup-', [status(thm)], ['15', '21'])).
% 1.51/1.74  thf(t83_xboole_1, axiom,
% 1.51/1.74    (![A:$i,B:$i]:
% 1.51/1.74     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.51/1.74  thf('23', plain,
% 1.51/1.74      (![X19 : $i, X20 : $i]:
% 1.51/1.74         (((k4_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_xboole_0 @ X19 @ X20))),
% 1.51/1.74      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.51/1.74  thf('24', plain,
% 1.51/1.74      (![X0 : $i, X1 : $i]:
% 1.51/1.74         ((r2_hidden @ X0 @ X1)
% 1.51/1.74          | ((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1)))),
% 1.51/1.74      inference('sup-', [status(thm)], ['22', '23'])).
% 1.51/1.74  thf('25', plain,
% 1.51/1.74      (((sk_B_1)
% 1.51/1.74         != (k2_yellow19 @ sk_A @ 
% 1.51/1.74             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 1.51/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.74  thf('26', plain,
% 1.51/1.74      ((m1_subset_1 @ sk_B_1 @ 
% 1.51/1.74        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 1.51/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.74  thf(d2_yellow_1, axiom,
% 1.51/1.74    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 1.51/1.74  thf('27', plain,
% 1.51/1.74      (![X32 : $i]: ((k3_yellow_1 @ X32) = (k3_lattice3 @ (k1_lattice3 @ X32)))),
% 1.51/1.74      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.51/1.74  thf('28', plain,
% 1.51/1.74      ((m1_subset_1 @ sk_B_1 @ 
% 1.51/1.74        (k1_zfmisc_1 @ 
% 1.51/1.74         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 1.51/1.74      inference('demod', [status(thm)], ['26', '27'])).
% 1.51/1.74  thf(t14_yellow19, axiom,
% 1.51/1.74    (![A:$i]:
% 1.51/1.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.51/1.74       ( ![B:$i]:
% 1.51/1.74         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 1.51/1.74             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 1.51/1.74             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 1.51/1.74             ( m1_subset_1 @
% 1.51/1.74               B @ 
% 1.51/1.74               ( k1_zfmisc_1 @
% 1.51/1.74                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 1.51/1.74           ( ( k7_subset_1 @
% 1.51/1.74               ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ 
% 1.51/1.74               ( k1_tarski @ k1_xboole_0 ) ) =
% 1.51/1.74             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 1.51/1.74  thf('29', plain,
% 1.51/1.74      (![X33 : $i, X34 : $i]:
% 1.51/1.74         ((v1_xboole_0 @ X33)
% 1.51/1.74          | ~ (v2_waybel_0 @ X33 @ (k3_yellow_1 @ (k2_struct_0 @ X34)))
% 1.51/1.74          | ~ (v13_waybel_0 @ X33 @ (k3_yellow_1 @ (k2_struct_0 @ X34)))
% 1.51/1.74          | ~ (m1_subset_1 @ X33 @ 
% 1.51/1.74               (k1_zfmisc_1 @ 
% 1.51/1.74                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X34)))))
% 1.51/1.74          | ((k7_subset_1 @ 
% 1.51/1.74              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X34))) @ X33 @ 
% 1.51/1.74              (k1_tarski @ k1_xboole_0))
% 1.51/1.74              = (k2_yellow19 @ X34 @ 
% 1.51/1.74                 (k3_yellow19 @ X34 @ (k2_struct_0 @ X34) @ X33)))
% 1.51/1.74          | ~ (l1_struct_0 @ X34)
% 1.51/1.74          | (v2_struct_0 @ X34))),
% 1.51/1.74      inference('cnf', [status(esa)], [t14_yellow19])).
% 1.51/1.74  thf('30', plain,
% 1.51/1.74      (![X32 : $i]: ((k3_yellow_1 @ X32) = (k3_lattice3 @ (k1_lattice3 @ X32)))),
% 1.51/1.74      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.51/1.74  thf('31', plain,
% 1.51/1.74      (![X32 : $i]: ((k3_yellow_1 @ X32) = (k3_lattice3 @ (k1_lattice3 @ X32)))),
% 1.51/1.74      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.51/1.74  thf('32', plain,
% 1.51/1.74      (![X32 : $i]: ((k3_yellow_1 @ X32) = (k3_lattice3 @ (k1_lattice3 @ X32)))),
% 1.51/1.74      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.51/1.74  thf('33', plain,
% 1.51/1.74      (![X32 : $i]: ((k3_yellow_1 @ X32) = (k3_lattice3 @ (k1_lattice3 @ X32)))),
% 1.51/1.74      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.51/1.74  thf('34', plain,
% 1.51/1.74      (![X33 : $i, X34 : $i]:
% 1.51/1.74         ((v1_xboole_0 @ X33)
% 1.51/1.74          | ~ (v2_waybel_0 @ X33 @ 
% 1.51/1.74               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X34))))
% 1.51/1.74          | ~ (v13_waybel_0 @ X33 @ 
% 1.51/1.74               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X34))))
% 1.51/1.74          | ~ (m1_subset_1 @ X33 @ 
% 1.51/1.74               (k1_zfmisc_1 @ 
% 1.51/1.74                (u1_struct_0 @ 
% 1.51/1.74                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X34))))))
% 1.51/1.74          | ((k7_subset_1 @ 
% 1.51/1.74              (u1_struct_0 @ 
% 1.51/1.74               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X34)))) @ 
% 1.51/1.74              X33 @ (k1_tarski @ k1_xboole_0))
% 1.51/1.74              = (k2_yellow19 @ X34 @ 
% 1.51/1.74                 (k3_yellow19 @ X34 @ (k2_struct_0 @ X34) @ X33)))
% 1.51/1.74          | ~ (l1_struct_0 @ X34)
% 1.51/1.74          | (v2_struct_0 @ X34))),
% 1.51/1.74      inference('demod', [status(thm)], ['29', '30', '31', '32', '33'])).
% 1.51/1.74  thf('35', plain,
% 1.51/1.74      (((v2_struct_0 @ sk_A)
% 1.51/1.74        | ~ (l1_struct_0 @ sk_A)
% 1.51/1.74        | ((k7_subset_1 @ 
% 1.51/1.74            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 1.51/1.74            sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 1.51/1.74            = (k2_yellow19 @ sk_A @ 
% 1.51/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 1.51/1.74        | ~ (v13_waybel_0 @ sk_B_1 @ 
% 1.51/1.74             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 1.51/1.74        | ~ (v2_waybel_0 @ sk_B_1 @ 
% 1.51/1.74             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 1.51/1.74        | (v1_xboole_0 @ sk_B_1))),
% 1.51/1.74      inference('sup-', [status(thm)], ['28', '34'])).
% 1.51/1.74  thf('36', plain, ((l1_struct_0 @ sk_A)),
% 1.51/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.74  thf('37', plain,
% 1.51/1.74      ((m1_subset_1 @ sk_B_1 @ 
% 1.51/1.74        (k1_zfmisc_1 @ 
% 1.51/1.74         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 1.51/1.74      inference('demod', [status(thm)], ['26', '27'])).
% 1.51/1.74  thf(redefinition_k7_subset_1, axiom,
% 1.51/1.74    (![A:$i,B:$i,C:$i]:
% 1.51/1.74     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.51/1.74       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.51/1.74  thf('38', plain,
% 1.51/1.74      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.51/1.74         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 1.51/1.74          | ((k7_subset_1 @ X29 @ X28 @ X30) = (k4_xboole_0 @ X28 @ X30)))),
% 1.51/1.74      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.51/1.74  thf('39', plain,
% 1.51/1.74      (![X0 : $i]:
% 1.51/1.74         ((k7_subset_1 @ 
% 1.51/1.74           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 1.51/1.74           sk_B_1 @ X0) = (k4_xboole_0 @ sk_B_1 @ X0))),
% 1.51/1.74      inference('sup-', [status(thm)], ['37', '38'])).
% 1.51/1.74  thf('40', plain,
% 1.51/1.74      ((v13_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 1.51/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.74  thf('41', plain,
% 1.51/1.74      (![X32 : $i]: ((k3_yellow_1 @ X32) = (k3_lattice3 @ (k1_lattice3 @ X32)))),
% 1.51/1.74      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.51/1.74  thf('42', plain,
% 1.51/1.74      ((v13_waybel_0 @ sk_B_1 @ 
% 1.51/1.74        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 1.51/1.74      inference('demod', [status(thm)], ['40', '41'])).
% 1.51/1.74  thf('43', plain,
% 1.51/1.74      ((v2_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 1.51/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.74  thf('44', plain,
% 1.51/1.74      (![X32 : $i]: ((k3_yellow_1 @ X32) = (k3_lattice3 @ (k1_lattice3 @ X32)))),
% 1.51/1.74      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.51/1.74  thf('45', plain,
% 1.51/1.74      ((v2_waybel_0 @ sk_B_1 @ 
% 1.51/1.74        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 1.51/1.74      inference('demod', [status(thm)], ['43', '44'])).
% 1.51/1.74  thf('46', plain,
% 1.51/1.74      (((v2_struct_0 @ sk_A)
% 1.51/1.74        | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 1.51/1.74            = (k2_yellow19 @ sk_A @ 
% 1.51/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 1.51/1.74        | (v1_xboole_0 @ sk_B_1))),
% 1.51/1.74      inference('demod', [status(thm)], ['35', '36', '39', '42', '45'])).
% 1.51/1.74  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 1.51/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.74  thf('48', plain,
% 1.51/1.74      (((v1_xboole_0 @ sk_B_1)
% 1.51/1.74        | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 1.51/1.74            = (k2_yellow19 @ sk_A @ 
% 1.51/1.74               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))),
% 1.51/1.74      inference('clc', [status(thm)], ['46', '47'])).
% 1.51/1.74  thf('49', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.51/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.74  thf('50', plain,
% 1.51/1.74      (((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 1.51/1.74         = (k2_yellow19 @ sk_A @ 
% 1.51/1.74            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 1.51/1.74      inference('clc', [status(thm)], ['48', '49'])).
% 1.51/1.74  thf('51', plain,
% 1.51/1.74      (((sk_B_1) != (k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0)))),
% 1.51/1.74      inference('demod', [status(thm)], ['25', '50'])).
% 1.51/1.74  thf('52', plain,
% 1.51/1.74      ((((sk_B_1) != (sk_B_1)) | (r2_hidden @ k1_xboole_0 @ sk_B_1))),
% 1.51/1.74      inference('sup-', [status(thm)], ['24', '51'])).
% 1.51/1.74  thf('53', plain, ((r2_hidden @ k1_xboole_0 @ sk_B_1)),
% 1.51/1.74      inference('simplify', [status(thm)], ['52'])).
% 1.51/1.74  thf('54', plain,
% 1.51/1.74      ((m1_subset_1 @ sk_B_1 @ 
% 1.51/1.74        (k1_zfmisc_1 @ 
% 1.51/1.74         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 1.51/1.74      inference('demod', [status(thm)], ['26', '27'])).
% 1.51/1.74  thf(t2_yellow19, axiom,
% 1.51/1.74    (![A:$i]:
% 1.51/1.74     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.51/1.74       ( ![B:$i]:
% 1.51/1.74         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 1.51/1.74             ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 1.51/1.74             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 1.51/1.74             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 1.51/1.74             ( m1_subset_1 @
% 1.51/1.74               B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 1.51/1.74           ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ))).
% 1.51/1.74  thf('55', plain,
% 1.51/1.74      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.51/1.74         ((v1_xboole_0 @ X35)
% 1.51/1.74          | ~ (v1_subset_1 @ X35 @ (u1_struct_0 @ (k3_yellow_1 @ X36)))
% 1.51/1.74          | ~ (v2_waybel_0 @ X35 @ (k3_yellow_1 @ X36))
% 1.51/1.74          | ~ (v13_waybel_0 @ X35 @ (k3_yellow_1 @ X36))
% 1.51/1.74          | ~ (m1_subset_1 @ X35 @ 
% 1.51/1.74               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X36))))
% 1.51/1.74          | ~ (r2_hidden @ X37 @ X35)
% 1.51/1.74          | ~ (v1_xboole_0 @ X37)
% 1.51/1.74          | (v1_xboole_0 @ X36))),
% 1.51/1.74      inference('cnf', [status(esa)], [t2_yellow19])).
% 1.51/1.74  thf('56', plain,
% 1.51/1.74      (![X32 : $i]: ((k3_yellow_1 @ X32) = (k3_lattice3 @ (k1_lattice3 @ X32)))),
% 1.51/1.74      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.51/1.74  thf('57', plain,
% 1.51/1.74      (![X32 : $i]: ((k3_yellow_1 @ X32) = (k3_lattice3 @ (k1_lattice3 @ X32)))),
% 1.51/1.74      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.51/1.74  thf('58', plain,
% 1.51/1.74      (![X32 : $i]: ((k3_yellow_1 @ X32) = (k3_lattice3 @ (k1_lattice3 @ X32)))),
% 1.51/1.74      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.51/1.74  thf('59', plain,
% 1.51/1.74      (![X32 : $i]: ((k3_yellow_1 @ X32) = (k3_lattice3 @ (k1_lattice3 @ X32)))),
% 1.51/1.74      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.51/1.74  thf('60', plain,
% 1.51/1.74      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.51/1.74         ((v1_xboole_0 @ X35)
% 1.51/1.74          | ~ (v1_subset_1 @ X35 @ 
% 1.51/1.74               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X36))))
% 1.51/1.74          | ~ (v2_waybel_0 @ X35 @ (k3_lattice3 @ (k1_lattice3 @ X36)))
% 1.51/1.74          | ~ (v13_waybel_0 @ X35 @ (k3_lattice3 @ (k1_lattice3 @ X36)))
% 1.51/1.74          | ~ (m1_subset_1 @ X35 @ 
% 1.51/1.74               (k1_zfmisc_1 @ 
% 1.51/1.74                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X36)))))
% 1.51/1.74          | ~ (r2_hidden @ X37 @ X35)
% 1.51/1.74          | ~ (v1_xboole_0 @ X37)
% 1.51/1.74          | (v1_xboole_0 @ X36))),
% 1.51/1.74      inference('demod', [status(thm)], ['55', '56', '57', '58', '59'])).
% 1.51/1.74  thf('61', plain,
% 1.51/1.74      (![X0 : $i]:
% 1.51/1.74         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.51/1.74          | ~ (v1_xboole_0 @ X0)
% 1.51/1.74          | ~ (r2_hidden @ X0 @ sk_B_1)
% 1.51/1.74          | ~ (v13_waybel_0 @ sk_B_1 @ 
% 1.51/1.74               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 1.51/1.74          | ~ (v2_waybel_0 @ sk_B_1 @ 
% 1.51/1.74               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 1.51/1.74          | ~ (v1_subset_1 @ sk_B_1 @ 
% 1.51/1.74               (u1_struct_0 @ 
% 1.51/1.74                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 1.51/1.74          | (v1_xboole_0 @ sk_B_1))),
% 1.51/1.74      inference('sup-', [status(thm)], ['54', '60'])).
% 1.51/1.74  thf('62', plain,
% 1.51/1.74      ((v13_waybel_0 @ sk_B_1 @ 
% 1.51/1.74        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 1.51/1.74      inference('demod', [status(thm)], ['40', '41'])).
% 1.51/1.74  thf('63', plain,
% 1.51/1.74      ((v2_waybel_0 @ sk_B_1 @ 
% 1.51/1.74        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 1.51/1.74      inference('demod', [status(thm)], ['43', '44'])).
% 1.51/1.74  thf('64', plain,
% 1.51/1.74      ((v1_subset_1 @ sk_B_1 @ 
% 1.51/1.74        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 1.51/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.74  thf('65', plain,
% 1.51/1.74      (![X32 : $i]: ((k3_yellow_1 @ X32) = (k3_lattice3 @ (k1_lattice3 @ X32)))),
% 1.51/1.74      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.51/1.74  thf('66', plain,
% 1.51/1.74      ((v1_subset_1 @ sk_B_1 @ 
% 1.51/1.74        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 1.51/1.74      inference('demod', [status(thm)], ['64', '65'])).
% 1.51/1.74  thf('67', plain,
% 1.51/1.74      (![X0 : $i]:
% 1.51/1.74         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.51/1.74          | ~ (v1_xboole_0 @ X0)
% 1.51/1.74          | ~ (r2_hidden @ X0 @ sk_B_1)
% 1.51/1.74          | (v1_xboole_0 @ sk_B_1))),
% 1.51/1.74      inference('demod', [status(thm)], ['61', '62', '63', '66'])).
% 1.51/1.74  thf('68', plain,
% 1.51/1.74      (((v1_xboole_0 @ sk_B_1)
% 1.51/1.74        | ~ (v1_xboole_0 @ k1_xboole_0)
% 1.51/1.74        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 1.51/1.74      inference('sup-', [status(thm)], ['53', '67'])).
% 1.51/1.74  thf('69', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.51/1.74      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.51/1.74  thf('70', plain,
% 1.51/1.74      (((v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 1.51/1.74      inference('demod', [status(thm)], ['68', '69'])).
% 1.51/1.74  thf('71', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.51/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.74  thf('72', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 1.51/1.74      inference('clc', [status(thm)], ['70', '71'])).
% 1.51/1.74  thf(fc5_struct_0, axiom,
% 1.51/1.74    (![A:$i]:
% 1.51/1.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.51/1.74       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 1.51/1.74  thf('73', plain,
% 1.51/1.74      (![X31 : $i]:
% 1.51/1.74         (~ (v1_xboole_0 @ (k2_struct_0 @ X31))
% 1.51/1.74          | ~ (l1_struct_0 @ X31)
% 1.51/1.74          | (v2_struct_0 @ X31))),
% 1.51/1.74      inference('cnf', [status(esa)], [fc5_struct_0])).
% 1.51/1.74  thf('74', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 1.51/1.74      inference('sup-', [status(thm)], ['72', '73'])).
% 1.51/1.74  thf('75', plain, ((l1_struct_0 @ sk_A)),
% 1.51/1.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.74  thf('76', plain, ((v2_struct_0 @ sk_A)),
% 1.51/1.74      inference('demod', [status(thm)], ['74', '75'])).
% 1.51/1.74  thf('77', plain, ($false), inference('demod', [status(thm)], ['0', '76'])).
% 1.51/1.74  
% 1.51/1.74  % SZS output end Refutation
% 1.51/1.74  
% 1.51/1.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
