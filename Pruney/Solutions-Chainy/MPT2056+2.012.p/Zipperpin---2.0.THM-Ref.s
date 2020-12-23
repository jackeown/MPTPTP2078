%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UoUAtSAood

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:41 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 178 expanded)
%              Number of leaves         :   41 (  75 expanded)
%              Depth                    :   18
%              Number of atoms          :  969 (2226 expanded)
%              Number of equality atoms :   50 (  99 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X23 ) @ ( k1_tarski @ X24 ) )
      | ( X23 = X24 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('3',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X21 ) @ X22 )
      | ~ ( r2_hidden @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('7',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('8',plain,(
    ! [X29: $i] :
      ( ( k3_yellow_1 @ X29 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('9',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

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

thf('10',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v1_xboole_0 @ X32 )
      | ~ ( v1_subset_1 @ X32 @ ( u1_struct_0 @ ( k3_yellow_1 @ X33 ) ) )
      | ~ ( v2_waybel_0 @ X32 @ ( k3_yellow_1 @ X33 ) )
      | ~ ( v13_waybel_0 @ X32 @ ( k3_yellow_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X33 ) ) ) )
      | ~ ( r2_hidden @ X34 @ X32 )
      | ~ ( v1_xboole_0 @ X34 )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t2_yellow19])).

thf('11',plain,(
    ! [X29: $i] :
      ( ( k3_yellow_1 @ X29 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('12',plain,(
    ! [X29: $i] :
      ( ( k3_yellow_1 @ X29 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('13',plain,(
    ! [X29: $i] :
      ( ( k3_yellow_1 @ X29 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('14',plain,(
    ! [X29: $i] :
      ( ( k3_yellow_1 @ X29 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('15',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v1_xboole_0 @ X32 )
      | ~ ( v1_subset_1 @ X32 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X33 ) ) ) )
      | ~ ( v2_waybel_0 @ X32 @ ( k3_lattice3 @ ( k1_lattice3 @ X33 ) ) )
      | ~ ( v13_waybel_0 @ X32 @ ( k3_lattice3 @ ( k1_lattice3 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X33 ) ) ) ) )
      | ~ ( r2_hidden @ X34 @ X32 )
      | ~ ( v1_xboole_0 @ X34 )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(demod,[status(thm)],['10','11','12','13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf('17',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X29: $i] :
      ( ( k3_yellow_1 @ X29 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('19',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X29: $i] :
      ( ( k3_yellow_1 @ X29 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('22',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X29: $i] :
      ( ( k3_yellow_1 @ X29 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('25',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['16','19','22','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ ( sk_C @ sk_B_1 @ X0 ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['5','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('30',plain,(
    ! [X28: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('34',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('37',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ sk_B_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('40',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('41',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('42',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('49',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ X0 ) )
        = sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','50'])).

thf('52',plain,(
    sk_B_1
 != ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

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

thf('54',plain,(
    ! [X30: $i,X31: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( v2_waybel_0 @ X30 @ ( k3_yellow_1 @ ( k2_struct_0 @ X31 ) ) )
      | ~ ( v13_waybel_0 @ X30 @ ( k3_yellow_1 @ ( k2_struct_0 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X31 ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X31 ) ) ) @ X30 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X31 @ ( k3_yellow19 @ X31 @ ( k2_struct_0 @ X31 ) @ X30 ) ) )
      | ~ ( l1_struct_0 @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow19])).

thf('55',plain,(
    ! [X29: $i] :
      ( ( k3_yellow_1 @ X29 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('56',plain,(
    ! [X29: $i] :
      ( ( k3_yellow_1 @ X29 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('57',plain,(
    ! [X29: $i] :
      ( ( k3_yellow_1 @ X29 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('58',plain,(
    ! [X29: $i] :
      ( ( k3_yellow_1 @ X29 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('59',plain,(
    ! [X30: $i,X31: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( v2_waybel_0 @ X30 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X31 ) ) ) )
      | ~ ( v13_waybel_0 @ X30 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X31 ) ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X31 ) ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X31 ) ) ) ) @ X30 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X31 @ ( k3_yellow19 @ X31 @ ( k2_struct_0 @ X31 ) @ X30 ) ) )
      | ~ ( l1_struct_0 @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(demod,[status(thm)],['54','55','56','57','58'])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['53','59'])).

thf('61',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('63',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ( ( k7_subset_1 @ X26 @ X25 @ X27 )
        = ( k4_xboole_0 @ X25 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_1 @ X0 )
      = ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('66',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['60','61','64','65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    sk_B_1
 != ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['52','71'])).

thf('73',plain,
    ( ( sk_B_1 != sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','72'])).

thf('74',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('75',plain,
    ( ( sk_B_1 != sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    $false ),
    inference(demod,[status(thm)],['0','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UoUAtSAood
% 0.13/0.37  % Computer   : n012.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 19:22:37 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.36/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.61  % Solved by: fo/fo7.sh
% 0.36/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.61  % done 384 iterations in 0.124s
% 0.36/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.61  % SZS output start Refutation
% 0.36/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.36/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.61  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.36/0.61  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.36/0.61  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.36/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.61  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.36/0.61  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.36/0.61  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.36/0.61  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.36/0.61  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.36/0.61  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.36/0.61  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.36/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.61  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.36/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.61  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.36/0.61  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.36/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.61  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.36/0.61  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.36/0.61  thf(t15_yellow19, conjecture,
% 0.36/0.61    (![A:$i]:
% 0.36/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.36/0.61       ( ![B:$i]:
% 0.36/0.61         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.36/0.61             ( v1_subset_1 @
% 0.36/0.61               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.36/0.61             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.36/0.61             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.36/0.61             ( m1_subset_1 @
% 0.36/0.61               B @ 
% 0.36/0.61               ( k1_zfmisc_1 @
% 0.36/0.61                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.36/0.61           ( ( B ) =
% 0.36/0.61             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.36/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.61    (~( ![A:$i]:
% 0.36/0.61        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.36/0.61          ( ![B:$i]:
% 0.36/0.61            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.36/0.61                ( v1_subset_1 @
% 0.36/0.61                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.36/0.61                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.36/0.61                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.36/0.61                ( m1_subset_1 @
% 0.36/0.61                  B @ 
% 0.36/0.61                  ( k1_zfmisc_1 @
% 0.36/0.61                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.36/0.61              ( ( B ) =
% 0.36/0.61                ( k2_yellow19 @
% 0.36/0.61                  A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.36/0.61    inference('cnf.neg', [status(esa)], [t15_yellow19])).
% 0.36/0.61  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf(t3_xboole_0, axiom,
% 0.36/0.61    (![A:$i,B:$i]:
% 0.36/0.61     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.36/0.61            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.36/0.61       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.36/0.61            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.36/0.61  thf('1', plain,
% 0.36/0.61      (![X8 : $i, X9 : $i]:
% 0.36/0.61         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X8))),
% 0.36/0.61      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.36/0.61  thf(t17_zfmisc_1, axiom,
% 0.36/0.61    (![A:$i,B:$i]:
% 0.36/0.61     ( ( ( A ) != ( B ) ) =>
% 0.36/0.61       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.36/0.61  thf('2', plain,
% 0.36/0.61      (![X23 : $i, X24 : $i]:
% 0.36/0.61         ((r1_xboole_0 @ (k1_tarski @ X23) @ (k1_tarski @ X24))
% 0.36/0.61          | ((X23) = (X24)))),
% 0.36/0.61      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.36/0.61  thf(l24_zfmisc_1, axiom,
% 0.36/0.61    (![A:$i,B:$i]:
% 0.36/0.61     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.36/0.61  thf('3', plain,
% 0.36/0.61      (![X21 : $i, X22 : $i]:
% 0.36/0.61         (~ (r1_xboole_0 @ (k1_tarski @ X21) @ X22) | ~ (r2_hidden @ X21 @ X22))),
% 0.36/0.61      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.36/0.61  thf('4', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]:
% 0.36/0.61         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['2', '3'])).
% 0.36/0.61  thf('5', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]:
% 0.36/0.61         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.36/0.61          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['1', '4'])).
% 0.36/0.61  thf('6', plain,
% 0.36/0.61      (![X8 : $i, X9 : $i]:
% 0.36/0.61         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X9))),
% 0.36/0.61      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.36/0.61  thf('7', plain,
% 0.36/0.61      ((m1_subset_1 @ sk_B_1 @ 
% 0.36/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf(d2_yellow_1, axiom,
% 0.36/0.61    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.36/0.61  thf('8', plain,
% 0.36/0.61      (![X29 : $i]: ((k3_yellow_1 @ X29) = (k3_lattice3 @ (k1_lattice3 @ X29)))),
% 0.36/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.36/0.61  thf('9', plain,
% 0.36/0.61      ((m1_subset_1 @ sk_B_1 @ 
% 0.36/0.61        (k1_zfmisc_1 @ 
% 0.36/0.61         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.36/0.61      inference('demod', [status(thm)], ['7', '8'])).
% 0.36/0.61  thf(t2_yellow19, axiom,
% 0.36/0.61    (![A:$i]:
% 0.36/0.61     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.36/0.61       ( ![B:$i]:
% 0.36/0.61         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.36/0.61             ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 0.36/0.61             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.36/0.61             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.36/0.61             ( m1_subset_1 @
% 0.36/0.61               B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 0.36/0.61           ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ))).
% 0.36/0.61  thf('10', plain,
% 0.36/0.61      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.36/0.61         ((v1_xboole_0 @ X32)
% 0.36/0.61          | ~ (v1_subset_1 @ X32 @ (u1_struct_0 @ (k3_yellow_1 @ X33)))
% 0.36/0.61          | ~ (v2_waybel_0 @ X32 @ (k3_yellow_1 @ X33))
% 0.36/0.61          | ~ (v13_waybel_0 @ X32 @ (k3_yellow_1 @ X33))
% 0.36/0.61          | ~ (m1_subset_1 @ X32 @ 
% 0.36/0.61               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X33))))
% 0.36/0.61          | ~ (r2_hidden @ X34 @ X32)
% 0.36/0.61          | ~ (v1_xboole_0 @ X34)
% 0.36/0.61          | (v1_xboole_0 @ X33))),
% 0.36/0.61      inference('cnf', [status(esa)], [t2_yellow19])).
% 0.36/0.61  thf('11', plain,
% 0.36/0.61      (![X29 : $i]: ((k3_yellow_1 @ X29) = (k3_lattice3 @ (k1_lattice3 @ X29)))),
% 0.36/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.36/0.61  thf('12', plain,
% 0.36/0.61      (![X29 : $i]: ((k3_yellow_1 @ X29) = (k3_lattice3 @ (k1_lattice3 @ X29)))),
% 0.36/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.36/0.61  thf('13', plain,
% 0.36/0.61      (![X29 : $i]: ((k3_yellow_1 @ X29) = (k3_lattice3 @ (k1_lattice3 @ X29)))),
% 0.36/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.36/0.61  thf('14', plain,
% 0.36/0.61      (![X29 : $i]: ((k3_yellow_1 @ X29) = (k3_lattice3 @ (k1_lattice3 @ X29)))),
% 0.36/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.36/0.61  thf('15', plain,
% 0.36/0.61      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.36/0.61         ((v1_xboole_0 @ X32)
% 0.36/0.61          | ~ (v1_subset_1 @ X32 @ 
% 0.36/0.61               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X33))))
% 0.36/0.61          | ~ (v2_waybel_0 @ X32 @ (k3_lattice3 @ (k1_lattice3 @ X33)))
% 0.36/0.61          | ~ (v13_waybel_0 @ X32 @ (k3_lattice3 @ (k1_lattice3 @ X33)))
% 0.36/0.61          | ~ (m1_subset_1 @ X32 @ 
% 0.36/0.61               (k1_zfmisc_1 @ 
% 0.36/0.61                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X33)))))
% 0.36/0.61          | ~ (r2_hidden @ X34 @ X32)
% 0.36/0.61          | ~ (v1_xboole_0 @ X34)
% 0.36/0.61          | (v1_xboole_0 @ X33))),
% 0.36/0.61      inference('demod', [status(thm)], ['10', '11', '12', '13', '14'])).
% 0.36/0.61  thf('16', plain,
% 0.36/0.61      (![X0 : $i]:
% 0.36/0.61         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.36/0.61          | ~ (v1_xboole_0 @ X0)
% 0.36/0.61          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.36/0.61          | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.36/0.61               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.36/0.61          | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.36/0.61               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.36/0.61          | ~ (v1_subset_1 @ sk_B_1 @ 
% 0.36/0.61               (u1_struct_0 @ 
% 0.36/0.61                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.36/0.61          | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.61      inference('sup-', [status(thm)], ['9', '15'])).
% 0.36/0.61  thf('17', plain,
% 0.36/0.61      ((v13_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('18', plain,
% 0.36/0.61      (![X29 : $i]: ((k3_yellow_1 @ X29) = (k3_lattice3 @ (k1_lattice3 @ X29)))),
% 0.36/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.36/0.61  thf('19', plain,
% 0.36/0.61      ((v13_waybel_0 @ sk_B_1 @ 
% 0.36/0.61        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.36/0.61      inference('demod', [status(thm)], ['17', '18'])).
% 0.36/0.61  thf('20', plain,
% 0.36/0.61      ((v2_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('21', plain,
% 0.36/0.61      (![X29 : $i]: ((k3_yellow_1 @ X29) = (k3_lattice3 @ (k1_lattice3 @ X29)))),
% 0.36/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.36/0.61  thf('22', plain,
% 0.36/0.61      ((v2_waybel_0 @ sk_B_1 @ 
% 0.36/0.61        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.36/0.61      inference('demod', [status(thm)], ['20', '21'])).
% 0.36/0.61  thf('23', plain,
% 0.36/0.61      ((v1_subset_1 @ sk_B_1 @ 
% 0.36/0.61        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('24', plain,
% 0.36/0.61      (![X29 : $i]: ((k3_yellow_1 @ X29) = (k3_lattice3 @ (k1_lattice3 @ X29)))),
% 0.36/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.36/0.61  thf('25', plain,
% 0.36/0.61      ((v1_subset_1 @ sk_B_1 @ 
% 0.36/0.61        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.36/0.61      inference('demod', [status(thm)], ['23', '24'])).
% 0.36/0.61  thf('26', plain,
% 0.36/0.61      (![X0 : $i]:
% 0.36/0.61         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.36/0.61          | ~ (v1_xboole_0 @ X0)
% 0.36/0.61          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.36/0.61          | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.61      inference('demod', [status(thm)], ['16', '19', '22', '25'])).
% 0.36/0.61  thf('27', plain,
% 0.36/0.61      (![X0 : $i]:
% 0.36/0.61         ((r1_xboole_0 @ X0 @ sk_B_1)
% 0.36/0.61          | (v1_xboole_0 @ sk_B_1)
% 0.36/0.61          | ~ (v1_xboole_0 @ (sk_C @ sk_B_1 @ X0))
% 0.36/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['6', '26'])).
% 0.36/0.61  thf('28', plain,
% 0.36/0.61      (![X0 : $i]:
% 0.36/0.61         (~ (v1_xboole_0 @ X0)
% 0.36/0.61          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_1)
% 0.36/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.36/0.61          | (v1_xboole_0 @ sk_B_1)
% 0.36/0.61          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_1))),
% 0.36/0.61      inference('sup-', [status(thm)], ['5', '27'])).
% 0.36/0.61  thf('29', plain,
% 0.36/0.61      (![X0 : $i]:
% 0.36/0.61         ((v1_xboole_0 @ sk_B_1)
% 0.36/0.61          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.36/0.61          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_1)
% 0.36/0.61          | ~ (v1_xboole_0 @ X0))),
% 0.36/0.61      inference('simplify', [status(thm)], ['28'])).
% 0.36/0.61  thf(fc5_struct_0, axiom,
% 0.36/0.61    (![A:$i]:
% 0.36/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.36/0.61       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.36/0.61  thf('30', plain,
% 0.36/0.61      (![X28 : $i]:
% 0.36/0.61         (~ (v1_xboole_0 @ (k2_struct_0 @ X28))
% 0.36/0.61          | ~ (l1_struct_0 @ X28)
% 0.36/0.61          | (v2_struct_0 @ X28))),
% 0.36/0.61      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.36/0.61  thf('31', plain,
% 0.36/0.61      (![X0 : $i]:
% 0.36/0.61         (~ (v1_xboole_0 @ X0)
% 0.36/0.61          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_1)
% 0.36/0.61          | (v1_xboole_0 @ sk_B_1)
% 0.36/0.61          | (v2_struct_0 @ sk_A)
% 0.36/0.61          | ~ (l1_struct_0 @ sk_A))),
% 0.36/0.61      inference('sup-', [status(thm)], ['29', '30'])).
% 0.36/0.61  thf('32', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('33', plain,
% 0.36/0.61      (![X0 : $i]:
% 0.36/0.61         (~ (v1_xboole_0 @ X0)
% 0.36/0.61          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_1)
% 0.36/0.61          | (v1_xboole_0 @ sk_B_1)
% 0.36/0.61          | (v2_struct_0 @ sk_A))),
% 0.36/0.61      inference('demod', [status(thm)], ['31', '32'])).
% 0.36/0.61  thf(d7_xboole_0, axiom,
% 0.36/0.61    (![A:$i,B:$i]:
% 0.36/0.61     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.36/0.61       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.36/0.61  thf('34', plain,
% 0.36/0.61      (![X5 : $i, X6 : $i]:
% 0.36/0.61         (((k3_xboole_0 @ X5 @ X6) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X5 @ X6))),
% 0.36/0.61      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.36/0.61  thf('35', plain,
% 0.36/0.61      (![X0 : $i]:
% 0.36/0.61         ((v2_struct_0 @ sk_A)
% 0.36/0.61          | (v1_xboole_0 @ sk_B_1)
% 0.36/0.61          | ~ (v1_xboole_0 @ X0)
% 0.36/0.61          | ((k3_xboole_0 @ (k1_tarski @ X0) @ sk_B_1) = (k1_xboole_0)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['33', '34'])).
% 0.36/0.61  thf(commutativity_k3_xboole_0, axiom,
% 0.36/0.61    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.36/0.61  thf('36', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.36/0.61  thf(t100_xboole_1, axiom,
% 0.36/0.61    (![A:$i,B:$i]:
% 0.36/0.61     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.36/0.61  thf('37', plain,
% 0.36/0.61      (![X12 : $i, X13 : $i]:
% 0.36/0.61         ((k4_xboole_0 @ X12 @ X13)
% 0.36/0.61           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.36/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.36/0.61  thf('38', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]:
% 0.36/0.61         ((k4_xboole_0 @ X0 @ X1)
% 0.36/0.61           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.36/0.61      inference('sup+', [status(thm)], ['36', '37'])).
% 0.36/0.61  thf('39', plain,
% 0.36/0.61      (![X0 : $i]:
% 0.36/0.61         (((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ X0))
% 0.36/0.61            = (k5_xboole_0 @ sk_B_1 @ k1_xboole_0))
% 0.36/0.61          | ~ (v1_xboole_0 @ X0)
% 0.36/0.61          | (v1_xboole_0 @ sk_B_1)
% 0.36/0.61          | (v2_struct_0 @ sk_A))),
% 0.36/0.61      inference('sup+', [status(thm)], ['35', '38'])).
% 0.36/0.61  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.36/0.61  thf('40', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.61  thf('41', plain,
% 0.36/0.61      (![X8 : $i, X9 : $i]:
% 0.36/0.61         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X9))),
% 0.36/0.61      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.36/0.61  thf(d1_xboole_0, axiom,
% 0.36/0.61    (![A:$i]:
% 0.36/0.61     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.36/0.61  thf('42', plain,
% 0.36/0.61      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.36/0.61      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.36/0.61  thf('43', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.36/0.61      inference('sup-', [status(thm)], ['41', '42'])).
% 0.36/0.61  thf('44', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.36/0.61      inference('sup-', [status(thm)], ['40', '43'])).
% 0.36/0.61  thf('45', plain,
% 0.36/0.61      (![X5 : $i, X6 : $i]:
% 0.36/0.61         (((k3_xboole_0 @ X5 @ X6) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X5 @ X6))),
% 0.36/0.61      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.36/0.61  thf('46', plain,
% 0.36/0.61      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.61      inference('sup-', [status(thm)], ['44', '45'])).
% 0.36/0.61  thf('47', plain,
% 0.36/0.61      (![X12 : $i, X13 : $i]:
% 0.36/0.61         ((k4_xboole_0 @ X12 @ X13)
% 0.36/0.61           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.36/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.36/0.61  thf('48', plain,
% 0.36/0.61      (![X0 : $i]:
% 0.36/0.61         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.36/0.61      inference('sup+', [status(thm)], ['46', '47'])).
% 0.36/0.61  thf(t3_boole, axiom,
% 0.36/0.61    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.36/0.61  thf('49', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.36/0.61      inference('cnf', [status(esa)], [t3_boole])).
% 0.36/0.61  thf('50', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.36/0.61      inference('sup+', [status(thm)], ['48', '49'])).
% 0.36/0.61  thf('51', plain,
% 0.36/0.61      (![X0 : $i]:
% 0.36/0.61         (((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ X0)) = (sk_B_1))
% 0.36/0.61          | ~ (v1_xboole_0 @ X0)
% 0.36/0.61          | (v1_xboole_0 @ sk_B_1)
% 0.36/0.61          | (v2_struct_0 @ sk_A))),
% 0.36/0.61      inference('demod', [status(thm)], ['39', '50'])).
% 0.36/0.61  thf('52', plain,
% 0.36/0.61      (((sk_B_1)
% 0.36/0.61         != (k2_yellow19 @ sk_A @ 
% 0.36/0.61             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('53', plain,
% 0.36/0.61      ((m1_subset_1 @ sk_B_1 @ 
% 0.36/0.61        (k1_zfmisc_1 @ 
% 0.36/0.61         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.36/0.61      inference('demod', [status(thm)], ['7', '8'])).
% 0.36/0.61  thf(t14_yellow19, axiom,
% 0.36/0.61    (![A:$i]:
% 0.36/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.36/0.61       ( ![B:$i]:
% 0.36/0.61         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.36/0.61             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.36/0.61             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.36/0.61             ( m1_subset_1 @
% 0.36/0.61               B @ 
% 0.36/0.61               ( k1_zfmisc_1 @
% 0.36/0.61                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.36/0.61           ( ( k7_subset_1 @
% 0.36/0.61               ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ 
% 0.36/0.61               ( k1_tarski @ k1_xboole_0 ) ) =
% 0.36/0.61             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.36/0.61  thf('54', plain,
% 0.36/0.61      (![X30 : $i, X31 : $i]:
% 0.36/0.61         ((v1_xboole_0 @ X30)
% 0.36/0.61          | ~ (v2_waybel_0 @ X30 @ (k3_yellow_1 @ (k2_struct_0 @ X31)))
% 0.36/0.61          | ~ (v13_waybel_0 @ X30 @ (k3_yellow_1 @ (k2_struct_0 @ X31)))
% 0.36/0.61          | ~ (m1_subset_1 @ X30 @ 
% 0.36/0.61               (k1_zfmisc_1 @ 
% 0.36/0.61                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X31)))))
% 0.36/0.61          | ((k7_subset_1 @ 
% 0.36/0.61              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X31))) @ X30 @ 
% 0.36/0.61              (k1_tarski @ k1_xboole_0))
% 0.36/0.61              = (k2_yellow19 @ X31 @ 
% 0.36/0.61                 (k3_yellow19 @ X31 @ (k2_struct_0 @ X31) @ X30)))
% 0.36/0.61          | ~ (l1_struct_0 @ X31)
% 0.36/0.61          | (v2_struct_0 @ X31))),
% 0.36/0.61      inference('cnf', [status(esa)], [t14_yellow19])).
% 0.36/0.61  thf('55', plain,
% 0.36/0.61      (![X29 : $i]: ((k3_yellow_1 @ X29) = (k3_lattice3 @ (k1_lattice3 @ X29)))),
% 0.36/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.36/0.61  thf('56', plain,
% 0.36/0.61      (![X29 : $i]: ((k3_yellow_1 @ X29) = (k3_lattice3 @ (k1_lattice3 @ X29)))),
% 0.36/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.36/0.61  thf('57', plain,
% 0.36/0.61      (![X29 : $i]: ((k3_yellow_1 @ X29) = (k3_lattice3 @ (k1_lattice3 @ X29)))),
% 0.36/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.36/0.61  thf('58', plain,
% 0.36/0.61      (![X29 : $i]: ((k3_yellow_1 @ X29) = (k3_lattice3 @ (k1_lattice3 @ X29)))),
% 0.36/0.61      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.36/0.61  thf('59', plain,
% 0.36/0.61      (![X30 : $i, X31 : $i]:
% 0.36/0.61         ((v1_xboole_0 @ X30)
% 0.36/0.61          | ~ (v2_waybel_0 @ X30 @ 
% 0.36/0.61               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X31))))
% 0.36/0.61          | ~ (v13_waybel_0 @ X30 @ 
% 0.36/0.61               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X31))))
% 0.36/0.61          | ~ (m1_subset_1 @ X30 @ 
% 0.36/0.61               (k1_zfmisc_1 @ 
% 0.36/0.61                (u1_struct_0 @ 
% 0.36/0.61                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X31))))))
% 0.36/0.61          | ((k7_subset_1 @ 
% 0.36/0.61              (u1_struct_0 @ 
% 0.36/0.61               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X31)))) @ 
% 0.36/0.61              X30 @ (k1_tarski @ k1_xboole_0))
% 0.36/0.61              = (k2_yellow19 @ X31 @ 
% 0.36/0.61                 (k3_yellow19 @ X31 @ (k2_struct_0 @ X31) @ X30)))
% 0.36/0.61          | ~ (l1_struct_0 @ X31)
% 0.36/0.61          | (v2_struct_0 @ X31))),
% 0.36/0.61      inference('demod', [status(thm)], ['54', '55', '56', '57', '58'])).
% 0.36/0.61  thf('60', plain,
% 0.36/0.61      (((v2_struct_0 @ sk_A)
% 0.36/0.61        | ~ (l1_struct_0 @ sk_A)
% 0.36/0.61        | ((k7_subset_1 @ 
% 0.36/0.61            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.36/0.61            sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.36/0.61            = (k2_yellow19 @ sk_A @ 
% 0.36/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.36/0.61        | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.36/0.61             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.36/0.61        | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.36/0.61             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.36/0.61        | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.61      inference('sup-', [status(thm)], ['53', '59'])).
% 0.36/0.61  thf('61', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('62', plain,
% 0.36/0.61      ((m1_subset_1 @ sk_B_1 @ 
% 0.36/0.61        (k1_zfmisc_1 @ 
% 0.36/0.61         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.36/0.61      inference('demod', [status(thm)], ['7', '8'])).
% 0.36/0.61  thf(redefinition_k7_subset_1, axiom,
% 0.36/0.61    (![A:$i,B:$i,C:$i]:
% 0.36/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.61       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.36/0.61  thf('63', plain,
% 0.36/0.61      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.36/0.61         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 0.36/0.61          | ((k7_subset_1 @ X26 @ X25 @ X27) = (k4_xboole_0 @ X25 @ X27)))),
% 0.36/0.61      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.36/0.61  thf('64', plain,
% 0.36/0.61      (![X0 : $i]:
% 0.36/0.61         ((k7_subset_1 @ 
% 0.36/0.61           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.36/0.61           sk_B_1 @ X0) = (k4_xboole_0 @ sk_B_1 @ X0))),
% 0.36/0.61      inference('sup-', [status(thm)], ['62', '63'])).
% 0.36/0.61  thf('65', plain,
% 0.36/0.61      ((v13_waybel_0 @ sk_B_1 @ 
% 0.36/0.61        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.36/0.61      inference('demod', [status(thm)], ['17', '18'])).
% 0.36/0.61  thf('66', plain,
% 0.36/0.61      ((v2_waybel_0 @ sk_B_1 @ 
% 0.36/0.61        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.36/0.61      inference('demod', [status(thm)], ['20', '21'])).
% 0.36/0.61  thf('67', plain,
% 0.36/0.61      (((v2_struct_0 @ sk_A)
% 0.36/0.61        | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.36/0.61            = (k2_yellow19 @ sk_A @ 
% 0.36/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.36/0.61        | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.61      inference('demod', [status(thm)], ['60', '61', '64', '65', '66'])).
% 0.36/0.61  thf('68', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('69', plain,
% 0.36/0.61      (((v1_xboole_0 @ sk_B_1)
% 0.36/0.61        | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.36/0.61            = (k2_yellow19 @ sk_A @ 
% 0.36/0.61               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))),
% 0.36/0.61      inference('clc', [status(thm)], ['67', '68'])).
% 0.36/0.61  thf('70', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('71', plain,
% 0.36/0.61      (((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.36/0.61         = (k2_yellow19 @ sk_A @ 
% 0.36/0.61            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.36/0.61      inference('clc', [status(thm)], ['69', '70'])).
% 0.36/0.61  thf('72', plain,
% 0.36/0.61      (((sk_B_1) != (k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0)))),
% 0.36/0.61      inference('demod', [status(thm)], ['52', '71'])).
% 0.36/0.61  thf('73', plain,
% 0.36/0.61      ((((sk_B_1) != (sk_B_1))
% 0.36/0.61        | (v2_struct_0 @ sk_A)
% 0.36/0.61        | (v1_xboole_0 @ sk_B_1)
% 0.36/0.61        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.36/0.61      inference('sup-', [status(thm)], ['51', '72'])).
% 0.36/0.61  thf('74', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.61  thf('75', plain,
% 0.36/0.61      ((((sk_B_1) != (sk_B_1)) | (v2_struct_0 @ sk_A) | (v1_xboole_0 @ sk_B_1))),
% 0.36/0.61      inference('demod', [status(thm)], ['73', '74'])).
% 0.36/0.61  thf('76', plain, (((v1_xboole_0 @ sk_B_1) | (v2_struct_0 @ sk_A))),
% 0.36/0.61      inference('simplify', [status(thm)], ['75'])).
% 0.36/0.61  thf('77', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('78', plain, ((v2_struct_0 @ sk_A)),
% 0.36/0.61      inference('clc', [status(thm)], ['76', '77'])).
% 0.36/0.61  thf('79', plain, ($false), inference('demod', [status(thm)], ['0', '78'])).
% 0.36/0.61  
% 0.36/0.61  % SZS output end Refutation
% 0.36/0.61  
% 0.36/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
