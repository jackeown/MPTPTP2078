%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5f39ZYmxrv

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:47 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 153 expanded)
%              Number of leaves         :   35 (  65 expanded)
%              Depth                    :   17
%              Number of atoms          :  814 (2034 expanded)
%              Number of equality atoms :   36 (  83 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X11 ) @ ( k1_tarski @ X12 ) )
      | ( X11 = X12 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X9 ) @ X10 )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
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
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( v2_waybel_0 @ X18 @ ( k3_yellow_1 @ ( k2_struct_0 @ X19 ) ) )
      | ~ ( v13_waybel_0 @ X18 @ ( k3_yellow_1 @ ( k2_struct_0 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X19 ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X19 ) ) ) @ X18 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X19 @ ( k3_yellow19 @ X19 @ ( k2_struct_0 @ X19 ) @ X18 ) ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow19])).

thf('16',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('17',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('18',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('19',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('20',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( v2_waybel_0 @ X18 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X19 ) ) ) )
      | ~ ( v13_waybel_0 @ X18 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X19 ) ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X19 ) ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X19 ) ) ) ) @ X18 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X19 @ ( k3_yellow19 @ X19 @ ( k2_struct_0 @ X19 ) @ X18 ) ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
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
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('25',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('28',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['21','22','25','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('31',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( ( k7_subset_1 @ X14 @ X13 @ X15 )
        = ( k4_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    sk_B
 != ( k4_xboole_0 @ sk_B @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['11','37'])).

thf('39',plain,
    ( ( sk_B != sk_B )
    | ( r2_hidden @ k1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['10','38'])).

thf('40',plain,(
    r2_hidden @ k1_xboole_0 @ sk_B ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
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

thf('42',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ~ ( v1_subset_1 @ X20 @ ( u1_struct_0 @ ( k3_yellow_1 @ X21 ) ) )
      | ~ ( v2_waybel_0 @ X20 @ ( k3_yellow_1 @ X21 ) )
      | ~ ( v13_waybel_0 @ X20 @ ( k3_yellow_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X21 ) ) ) )
      | ~ ( r2_hidden @ X22 @ X20 )
      | ~ ( v1_xboole_0 @ X22 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t2_yellow19])).

thf('43',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('44',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ~ ( v1_subset_1 @ X20 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X21 ) ) ) )
      | ~ ( v2_waybel_0 @ X20 @ ( k3_lattice3 @ ( k1_lattice3 @ X21 ) ) )
      | ~ ( v13_waybel_0 @ X20 @ ( k3_lattice3 @ ( k1_lattice3 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X21 ) ) ) ) )
      | ~ ( r2_hidden @ X22 @ X20 )
      | ~ ( v1_xboole_0 @ X22 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(demod,[status(thm)],['42','43','44','45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','47'])).

thf('49',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('50',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('51',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('53',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','49','50','53'])).

thf('55',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','54'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('56',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('57',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['57','58'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('60',plain,(
    ! [X16: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    $false ),
    inference(demod,[status(thm)],['0','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5f39ZYmxrv
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:09:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 57 iterations in 0.029s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.50  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.50  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.22/0.50  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.22/0.50  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.22/0.50  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.50  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.22/0.50  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.22/0.50  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.22/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.22/0.50  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.50  thf(t15_yellow19, conjecture,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.22/0.50             ( v1_subset_1 @
% 0.22/0.50               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.22/0.50             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.22/0.50             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.22/0.50             ( m1_subset_1 @
% 0.22/0.50               B @ 
% 0.22/0.50               ( k1_zfmisc_1 @
% 0.22/0.50                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.22/0.50           ( ( B ) =
% 0.22/0.50             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i]:
% 0.22/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.50          ( ![B:$i]:
% 0.22/0.50            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.22/0.50                ( v1_subset_1 @
% 0.22/0.50                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.22/0.50                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.22/0.50                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.22/0.50                ( m1_subset_1 @
% 0.22/0.50                  B @ 
% 0.22/0.50                  ( k1_zfmisc_1 @
% 0.22/0.50                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.22/0.50              ( ( B ) =
% 0.22/0.50                ( k2_yellow19 @
% 0.22/0.50                  A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t15_yellow19])).
% 0.22/0.50  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t3_xboole_0, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.22/0.50            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.50       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.22/0.50            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.22/0.50      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.50  thf(t17_zfmisc_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( A ) != ( B ) ) =>
% 0.22/0.50       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      (![X11 : $i, X12 : $i]:
% 0.22/0.50         ((r1_xboole_0 @ (k1_tarski @ X11) @ (k1_tarski @ X12))
% 0.22/0.50          | ((X11) = (X12)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.22/0.50  thf(l24_zfmisc_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      (![X9 : $i, X10 : $i]:
% 0.22/0.50         (~ (r1_xboole_0 @ (k1_tarski @ X9) @ X10) | ~ (r2_hidden @ X9 @ X10))),
% 0.22/0.50      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.22/0.50          | ((sk_C @ (k1_tarski @ X0) @ X1) = (X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['1', '4'])).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((r2_hidden @ X0 @ X1)
% 0.22/0.50          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.22/0.50          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.22/0.50      inference('sup+', [status(thm)], ['5', '6'])).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0)) | (r2_hidden @ X0 @ X1))),
% 0.22/0.50      inference('simplify', [status(thm)], ['7'])).
% 0.22/0.50  thf(t83_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      (![X6 : $i, X7 : $i]:
% 0.22/0.50         (((k4_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 0.22/0.50      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((r2_hidden @ X0 @ X1)
% 0.22/0.50          | ((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      (((sk_B)
% 0.22/0.50         != (k2_yellow19 @ sk_A @ 
% 0.22/0.50             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_B @ 
% 0.22/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(d2_yellow_1, axiom,
% 0.22/0.50    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_B @ 
% 0.22/0.50        (k1_zfmisc_1 @ 
% 0.22/0.50         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.22/0.50      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.50  thf(t14_yellow19, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.22/0.50             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.22/0.50             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.22/0.50             ( m1_subset_1 @
% 0.22/0.50               B @ 
% 0.22/0.50               ( k1_zfmisc_1 @
% 0.22/0.50                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.22/0.50           ( ( k7_subset_1 @
% 0.22/0.50               ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ 
% 0.22/0.50               ( k1_tarski @ k1_xboole_0 ) ) =
% 0.22/0.50             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      (![X18 : $i, X19 : $i]:
% 0.22/0.50         ((v1_xboole_0 @ X18)
% 0.22/0.50          | ~ (v2_waybel_0 @ X18 @ (k3_yellow_1 @ (k2_struct_0 @ X19)))
% 0.22/0.50          | ~ (v13_waybel_0 @ X18 @ (k3_yellow_1 @ (k2_struct_0 @ X19)))
% 0.22/0.50          | ~ (m1_subset_1 @ X18 @ 
% 0.22/0.50               (k1_zfmisc_1 @ 
% 0.22/0.50                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X19)))))
% 0.22/0.50          | ((k7_subset_1 @ 
% 0.22/0.50              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X19))) @ X18 @ 
% 0.22/0.50              (k1_tarski @ k1_xboole_0))
% 0.22/0.50              = (k2_yellow19 @ X19 @ 
% 0.22/0.50                 (k3_yellow19 @ X19 @ (k2_struct_0 @ X19) @ X18)))
% 0.22/0.50          | ~ (l1_struct_0 @ X19)
% 0.22/0.50          | (v2_struct_0 @ X19))),
% 0.22/0.50      inference('cnf', [status(esa)], [t14_yellow19])).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.22/0.50  thf('17', plain,
% 0.22/0.50      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.22/0.50  thf('18', plain,
% 0.22/0.50      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.22/0.50  thf('19', plain,
% 0.22/0.50      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.22/0.50  thf('20', plain,
% 0.22/0.50      (![X18 : $i, X19 : $i]:
% 0.22/0.50         ((v1_xboole_0 @ X18)
% 0.22/0.50          | ~ (v2_waybel_0 @ X18 @ 
% 0.22/0.50               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X19))))
% 0.22/0.50          | ~ (v13_waybel_0 @ X18 @ 
% 0.22/0.50               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X19))))
% 0.22/0.50          | ~ (m1_subset_1 @ X18 @ 
% 0.22/0.50               (k1_zfmisc_1 @ 
% 0.22/0.50                (u1_struct_0 @ 
% 0.22/0.50                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X19))))))
% 0.22/0.50          | ((k7_subset_1 @ 
% 0.22/0.50              (u1_struct_0 @ 
% 0.22/0.50               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X19)))) @ 
% 0.22/0.50              X18 @ (k1_tarski @ k1_xboole_0))
% 0.22/0.50              = (k2_yellow19 @ X19 @ 
% 0.22/0.50                 (k3_yellow19 @ X19 @ (k2_struct_0 @ X19) @ X18)))
% 0.22/0.50          | ~ (l1_struct_0 @ X19)
% 0.22/0.50          | (v2_struct_0 @ X19))),
% 0.22/0.50      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 0.22/0.50  thf('21', plain,
% 0.22/0.50      (((v2_struct_0 @ sk_A)
% 0.22/0.50        | ~ (l1_struct_0 @ sk_A)
% 0.22/0.50        | ((k7_subset_1 @ 
% 0.22/0.50            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.22/0.50            sk_B @ (k1_tarski @ k1_xboole_0))
% 0.22/0.50            = (k2_yellow19 @ sk_A @ 
% 0.22/0.50               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.22/0.50        | ~ (v13_waybel_0 @ sk_B @ 
% 0.22/0.50             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.22/0.50        | ~ (v2_waybel_0 @ sk_B @ 
% 0.22/0.50             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.22/0.50        | (v1_xboole_0 @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['14', '20'])).
% 0.22/0.50  thf('22', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('23', plain,
% 0.22/0.50      ((v13_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('24', plain,
% 0.22/0.50      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.22/0.50  thf('25', plain,
% 0.22/0.50      ((v13_waybel_0 @ sk_B @ 
% 0.22/0.50        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.22/0.50      inference('demod', [status(thm)], ['23', '24'])).
% 0.22/0.50  thf('26', plain,
% 0.22/0.50      ((v2_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('27', plain,
% 0.22/0.50      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.22/0.50  thf('28', plain,
% 0.22/0.50      ((v2_waybel_0 @ sk_B @ 
% 0.22/0.50        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.22/0.50      inference('demod', [status(thm)], ['26', '27'])).
% 0.22/0.50  thf('29', plain,
% 0.22/0.50      (((v2_struct_0 @ sk_A)
% 0.22/0.50        | ((k7_subset_1 @ 
% 0.22/0.50            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.22/0.50            sk_B @ (k1_tarski @ k1_xboole_0))
% 0.22/0.50            = (k2_yellow19 @ sk_A @ 
% 0.22/0.50               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.22/0.50        | (v1_xboole_0 @ sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['21', '22', '25', '28'])).
% 0.22/0.50  thf('30', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_B @ 
% 0.22/0.50        (k1_zfmisc_1 @ 
% 0.22/0.50         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.22/0.50      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.50  thf(redefinition_k7_subset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.50       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.22/0.50  thf('31', plain,
% 0.22/0.50      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.22/0.50          | ((k7_subset_1 @ X14 @ X13 @ X15) = (k4_xboole_0 @ X13 @ X15)))),
% 0.22/0.50      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.22/0.50  thf('32', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((k7_subset_1 @ 
% 0.22/0.50           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.22/0.50           sk_B @ X0) = (k4_xboole_0 @ sk_B @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['30', '31'])).
% 0.22/0.50  thf('33', plain,
% 0.22/0.50      (((v2_struct_0 @ sk_A)
% 0.22/0.50        | ((k4_xboole_0 @ sk_B @ (k1_tarski @ k1_xboole_0))
% 0.22/0.50            = (k2_yellow19 @ sk_A @ 
% 0.22/0.50               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.22/0.50        | (v1_xboole_0 @ sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['29', '32'])).
% 0.22/0.50  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('35', plain,
% 0.22/0.50      (((v1_xboole_0 @ sk_B)
% 0.22/0.50        | ((k4_xboole_0 @ sk_B @ (k1_tarski @ k1_xboole_0))
% 0.22/0.50            = (k2_yellow19 @ sk_A @ 
% 0.22/0.50               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.22/0.50      inference('clc', [status(thm)], ['33', '34'])).
% 0.22/0.50  thf('36', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('37', plain,
% 0.22/0.50      (((k4_xboole_0 @ sk_B @ (k1_tarski @ k1_xboole_0))
% 0.22/0.50         = (k2_yellow19 @ sk_A @ 
% 0.22/0.50            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.22/0.50      inference('clc', [status(thm)], ['35', '36'])).
% 0.22/0.50  thf('38', plain,
% 0.22/0.50      (((sk_B) != (k4_xboole_0 @ sk_B @ (k1_tarski @ k1_xboole_0)))),
% 0.22/0.50      inference('demod', [status(thm)], ['11', '37'])).
% 0.22/0.50  thf('39', plain, ((((sk_B) != (sk_B)) | (r2_hidden @ k1_xboole_0 @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['10', '38'])).
% 0.22/0.50  thf('40', plain, ((r2_hidden @ k1_xboole_0 @ sk_B)),
% 0.22/0.50      inference('simplify', [status(thm)], ['39'])).
% 0.22/0.50  thf('41', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_B @ 
% 0.22/0.50        (k1_zfmisc_1 @ 
% 0.22/0.50         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.22/0.50      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.50  thf(t2_yellow19, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.22/0.50             ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 0.22/0.50             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.22/0.50             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.22/0.50             ( m1_subset_1 @
% 0.22/0.50               B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 0.22/0.50           ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ))).
% 0.22/0.50  thf('42', plain,
% 0.22/0.50      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.50         ((v1_xboole_0 @ X20)
% 0.22/0.50          | ~ (v1_subset_1 @ X20 @ (u1_struct_0 @ (k3_yellow_1 @ X21)))
% 0.22/0.50          | ~ (v2_waybel_0 @ X20 @ (k3_yellow_1 @ X21))
% 0.22/0.50          | ~ (v13_waybel_0 @ X20 @ (k3_yellow_1 @ X21))
% 0.22/0.50          | ~ (m1_subset_1 @ X20 @ 
% 0.22/0.50               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X21))))
% 0.22/0.50          | ~ (r2_hidden @ X22 @ X20)
% 0.22/0.50          | ~ (v1_xboole_0 @ X22)
% 0.22/0.50          | (v1_xboole_0 @ X21))),
% 0.22/0.50      inference('cnf', [status(esa)], [t2_yellow19])).
% 0.22/0.50  thf('43', plain,
% 0.22/0.50      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.22/0.50  thf('44', plain,
% 0.22/0.50      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.22/0.50  thf('45', plain,
% 0.22/0.50      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.22/0.50  thf('46', plain,
% 0.22/0.50      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.22/0.50  thf('47', plain,
% 0.22/0.50      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.50         ((v1_xboole_0 @ X20)
% 0.22/0.50          | ~ (v1_subset_1 @ X20 @ 
% 0.22/0.50               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X21))))
% 0.22/0.50          | ~ (v2_waybel_0 @ X20 @ (k3_lattice3 @ (k1_lattice3 @ X21)))
% 0.22/0.50          | ~ (v13_waybel_0 @ X20 @ (k3_lattice3 @ (k1_lattice3 @ X21)))
% 0.22/0.50          | ~ (m1_subset_1 @ X20 @ 
% 0.22/0.50               (k1_zfmisc_1 @ 
% 0.22/0.50                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X21)))))
% 0.22/0.50          | ~ (r2_hidden @ X22 @ X20)
% 0.22/0.50          | ~ (v1_xboole_0 @ X22)
% 0.22/0.50          | (v1_xboole_0 @ X21))),
% 0.22/0.50      inference('demod', [status(thm)], ['42', '43', '44', '45', '46'])).
% 0.22/0.50  thf('48', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.22/0.50          | ~ (v1_xboole_0 @ X0)
% 0.22/0.50          | ~ (r2_hidden @ X0 @ sk_B)
% 0.22/0.50          | ~ (v13_waybel_0 @ sk_B @ 
% 0.22/0.50               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.22/0.50          | ~ (v2_waybel_0 @ sk_B @ 
% 0.22/0.50               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.22/0.50          | ~ (v1_subset_1 @ sk_B @ 
% 0.22/0.50               (u1_struct_0 @ 
% 0.22/0.50                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.22/0.50          | (v1_xboole_0 @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['41', '47'])).
% 0.22/0.50  thf('49', plain,
% 0.22/0.50      ((v13_waybel_0 @ sk_B @ 
% 0.22/0.50        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.22/0.50      inference('demod', [status(thm)], ['23', '24'])).
% 0.22/0.50  thf('50', plain,
% 0.22/0.50      ((v2_waybel_0 @ sk_B @ 
% 0.22/0.50        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.22/0.50      inference('demod', [status(thm)], ['26', '27'])).
% 0.22/0.50  thf('51', plain,
% 0.22/0.50      ((v1_subset_1 @ sk_B @ 
% 0.22/0.50        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('52', plain,
% 0.22/0.50      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k3_lattice3 @ (k1_lattice3 @ X17)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.22/0.50  thf('53', plain,
% 0.22/0.50      ((v1_subset_1 @ sk_B @ 
% 0.22/0.50        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.22/0.50      inference('demod', [status(thm)], ['51', '52'])).
% 0.22/0.50  thf('54', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.22/0.50          | ~ (v1_xboole_0 @ X0)
% 0.22/0.50          | ~ (r2_hidden @ X0 @ sk_B)
% 0.22/0.50          | (v1_xboole_0 @ sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['48', '49', '50', '53'])).
% 0.22/0.50  thf('55', plain,
% 0.22/0.50      (((v1_xboole_0 @ sk_B)
% 0.22/0.50        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.22/0.50        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['40', '54'])).
% 0.22/0.50  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.22/0.50  thf('56', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.50  thf('57', plain,
% 0.22/0.50      (((v1_xboole_0 @ sk_B) | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.22/0.50      inference('demod', [status(thm)], ['55', '56'])).
% 0.22/0.50  thf('58', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('59', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 0.22/0.50      inference('clc', [status(thm)], ['57', '58'])).
% 0.22/0.50  thf(fc5_struct_0, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.50       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.22/0.50  thf('60', plain,
% 0.22/0.50      (![X16 : $i]:
% 0.22/0.50         (~ (v1_xboole_0 @ (k2_struct_0 @ X16))
% 0.22/0.50          | ~ (l1_struct_0 @ X16)
% 0.22/0.50          | (v2_struct_0 @ X16))),
% 0.22/0.50      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.22/0.50  thf('61', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['59', '60'])).
% 0.22/0.50  thf('62', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('63', plain, ((v2_struct_0 @ sk_A)),
% 0.22/0.50      inference('demod', [status(thm)], ['61', '62'])).
% 0.22/0.50  thf('64', plain, ($false), inference('demod', [status(thm)], ['0', '63'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
