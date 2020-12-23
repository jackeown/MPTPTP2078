%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oGKiwMon6k

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 153 expanded)
%              Number of leaves         :   35 (  65 expanded)
%              Depth                    :   16
%              Number of atoms          :  851 (2071 expanded)
%              Number of equality atoms :   37 (  84 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

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
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
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
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X12 ) @ ( k1_tarski @ X13 ) )
      | ( X12 = X13 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X10 ) @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('7',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('8',plain,(
    ! [X18: $i] :
      ( ( k3_yellow_1 @ X18 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X18 ) ) ) ),
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

thf('11',plain,(
    ! [X18: $i] :
      ( ( k3_yellow_1 @ X18 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('12',plain,(
    ! [X18: $i] :
      ( ( k3_yellow_1 @ X18 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('13',plain,(
    ! [X18: $i] :
      ( ( k3_yellow_1 @ X18 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('14',plain,(
    ! [X18: $i] :
      ( ( k3_yellow_1 @ X18 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('15',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X21 )
      | ~ ( v1_subset_1 @ X21 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X22 ) ) ) )
      | ~ ( v2_waybel_0 @ X21 @ ( k3_lattice3 @ ( k1_lattice3 @ X22 ) ) )
      | ~ ( v13_waybel_0 @ X21 @ ( k3_lattice3 @ ( k1_lattice3 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X22 ) ) ) ) )
      | ~ ( r2_hidden @ X23 @ X21 )
      | ~ ( v1_xboole_0 @ X23 )
      | ( v1_xboole_0 @ X22 ) ) ),
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
    ! [X18: $i] :
      ( ( k3_yellow_1 @ X18 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('19',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X18: $i] :
      ( ( k3_yellow_1 @ X18 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('22',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X18: $i] :
      ( ( k3_yellow_1 @ X18 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X18 ) ) ) ),
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
      ( ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ ( sk_C @ X0 @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ sk_B_1 @ ( k1_tarski @ X0 ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( r1_xboole_0 @ sk_B_1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_xboole_0 @ sk_B_1 @ ( k1_tarski @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('30',plain,(
    ! [X17: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ sk_B_1 @ ( k1_tarski @ X0 ) )
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
      | ( r1_xboole_0 @ sk_B_1 @ ( k1_tarski @ X0 ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('34',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ X0 ) )
        = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    sk_B_1
 != ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
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

thf('38',plain,(
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

thf('39',plain,(
    ! [X18: $i] :
      ( ( k3_yellow_1 @ X18 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('40',plain,(
    ! [X18: $i] :
      ( ( k3_yellow_1 @ X18 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('41',plain,(
    ! [X18: $i] :
      ( ( k3_yellow_1 @ X18 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('42',plain,(
    ! [X18: $i] :
      ( ( k3_yellow_1 @ X18 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('43',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( v2_waybel_0 @ X19 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X20 ) ) ) )
      | ~ ( v13_waybel_0 @ X19 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X20 ) ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X20 ) ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X20 ) ) ) ) @ X19 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X20 @ ( k3_yellow19 @ X20 @ ( k2_struct_0 @ X20 ) @ X19 ) ) )
      | ~ ( l1_struct_0 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(demod,[status(thm)],['38','39','40','41','42'])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['37','43'])).

thf('45',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('47',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['44','45','46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('50',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( ( k7_subset_1 @ X15 @ X14 @ X16 )
        = ( k4_xboole_0 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_1 @ X0 )
      = ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['48','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    sk_B_1
 != ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['36','56'])).

thf('58',plain,
    ( ( sk_B_1 != sk_B_1 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','57'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('59',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('60',plain,
    ( ( sk_B_1 != sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    $false ),
    inference(demod,[status(thm)],['0','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oGKiwMon6k
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:37:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 62 iterations in 0.027s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.47  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.21/0.47  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.47  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.21/0.47  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.21/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.47  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.47  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.21/0.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.47  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.21/0.47  thf(t15_yellow19, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.47             ( v1_subset_1 @
% 0.21/0.47               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.21/0.47             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.47             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.47             ( m1_subset_1 @
% 0.21/0.47               B @ 
% 0.21/0.47               ( k1_zfmisc_1 @
% 0.21/0.47                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.21/0.47           ( ( B ) =
% 0.21/0.47             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.47          ( ![B:$i]:
% 0.21/0.47            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.47                ( v1_subset_1 @
% 0.21/0.47                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.21/0.47                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.47                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.47                ( m1_subset_1 @
% 0.21/0.47                  B @ 
% 0.21/0.47                  ( k1_zfmisc_1 @
% 0.21/0.47                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.21/0.47              ( ( B ) =
% 0.21/0.47                ( k2_yellow19 @
% 0.21/0.47                  A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t15_yellow19])).
% 0.21/0.47  thf('0', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t3_xboole_0, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.21/0.47            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.47       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.47            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X3 : $i, X4 : $i]:
% 0.21/0.47         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 0.21/0.47      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.47  thf(t17_zfmisc_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( A ) != ( B ) ) =>
% 0.21/0.47       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X12 : $i, X13 : $i]:
% 0.21/0.47         ((r1_xboole_0 @ (k1_tarski @ X12) @ (k1_tarski @ X13))
% 0.21/0.47          | ((X12) = (X13)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.21/0.47  thf(l24_zfmisc_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X10 : $i, X11 : $i]:
% 0.21/0.47         (~ (r1_xboole_0 @ (k1_tarski @ X10) @ X11) | ~ (r2_hidden @ X10 @ X11))),
% 0.21/0.47      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.21/0.47          | ((sk_C @ (k1_tarski @ X0) @ X1) = (X0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '4'])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X3 : $i, X4 : $i]:
% 0.21/0.47         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.21/0.47      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_B_1 @ 
% 0.21/0.47        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(d2_yellow_1, axiom,
% 0.21/0.47    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (![X18 : $i]: ((k3_yellow_1 @ X18) = (k3_lattice3 @ (k1_lattice3 @ X18)))),
% 0.21/0.47      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_B_1 @ 
% 0.21/0.47        (k1_zfmisc_1 @ 
% 0.21/0.47         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.21/0.47      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.47  thf(t2_yellow19, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.47             ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 0.21/0.47             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.21/0.47             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.21/0.47             ( m1_subset_1 @
% 0.21/0.47               B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 0.21/0.47           ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ))).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.47         ((v1_xboole_0 @ X21)
% 0.21/0.47          | ~ (v1_subset_1 @ X21 @ (u1_struct_0 @ (k3_yellow_1 @ X22)))
% 0.21/0.47          | ~ (v2_waybel_0 @ X21 @ (k3_yellow_1 @ X22))
% 0.21/0.47          | ~ (v13_waybel_0 @ X21 @ (k3_yellow_1 @ X22))
% 0.21/0.47          | ~ (m1_subset_1 @ X21 @ 
% 0.21/0.47               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X22))))
% 0.21/0.47          | ~ (r2_hidden @ X23 @ X21)
% 0.21/0.47          | ~ (v1_xboole_0 @ X23)
% 0.21/0.47          | (v1_xboole_0 @ X22))),
% 0.21/0.47      inference('cnf', [status(esa)], [t2_yellow19])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X18 : $i]: ((k3_yellow_1 @ X18) = (k3_lattice3 @ (k1_lattice3 @ X18)))),
% 0.21/0.47      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X18 : $i]: ((k3_yellow_1 @ X18) = (k3_lattice3 @ (k1_lattice3 @ X18)))),
% 0.21/0.47      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (![X18 : $i]: ((k3_yellow_1 @ X18) = (k3_lattice3 @ (k1_lattice3 @ X18)))),
% 0.21/0.47      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (![X18 : $i]: ((k3_yellow_1 @ X18) = (k3_lattice3 @ (k1_lattice3 @ X18)))),
% 0.21/0.47      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.47         ((v1_xboole_0 @ X21)
% 0.21/0.47          | ~ (v1_subset_1 @ X21 @ 
% 0.21/0.47               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X22))))
% 0.21/0.47          | ~ (v2_waybel_0 @ X21 @ (k3_lattice3 @ (k1_lattice3 @ X22)))
% 0.21/0.47          | ~ (v13_waybel_0 @ X21 @ (k3_lattice3 @ (k1_lattice3 @ X22)))
% 0.21/0.47          | ~ (m1_subset_1 @ X21 @ 
% 0.21/0.47               (k1_zfmisc_1 @ 
% 0.21/0.47                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X22)))))
% 0.21/0.47          | ~ (r2_hidden @ X23 @ X21)
% 0.21/0.47          | ~ (v1_xboole_0 @ X23)
% 0.21/0.47          | (v1_xboole_0 @ X22))),
% 0.21/0.47      inference('demod', [status(thm)], ['10', '11', '12', '13', '14'])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.47          | ~ (v1_xboole_0 @ X0)
% 0.21/0.47          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.21/0.47          | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.21/0.47               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.21/0.47          | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.21/0.47               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.21/0.47          | ~ (v1_subset_1 @ sk_B_1 @ 
% 0.21/0.47               (u1_struct_0 @ 
% 0.21/0.47                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.21/0.47          | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['9', '15'])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      ((v13_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      (![X18 : $i]: ((k3_yellow_1 @ X18) = (k3_lattice3 @ (k1_lattice3 @ X18)))),
% 0.21/0.47      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      ((v13_waybel_0 @ sk_B_1 @ 
% 0.21/0.47        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.47      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      ((v2_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('21', plain,
% 0.21/0.47      (![X18 : $i]: ((k3_yellow_1 @ X18) = (k3_lattice3 @ (k1_lattice3 @ X18)))),
% 0.21/0.47      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.47  thf('22', plain,
% 0.21/0.47      ((v2_waybel_0 @ sk_B_1 @ 
% 0.21/0.47        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.47      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.47  thf('23', plain,
% 0.21/0.47      ((v1_subset_1 @ sk_B_1 @ 
% 0.21/0.47        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('24', plain,
% 0.21/0.47      (![X18 : $i]: ((k3_yellow_1 @ X18) = (k3_lattice3 @ (k1_lattice3 @ X18)))),
% 0.21/0.47      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.47  thf('25', plain,
% 0.21/0.47      ((v1_subset_1 @ sk_B_1 @ 
% 0.21/0.47        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.21/0.47      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.47  thf('26', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.47          | ~ (v1_xboole_0 @ X0)
% 0.21/0.47          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.21/0.47          | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.47      inference('demod', [status(thm)], ['16', '19', '22', '25'])).
% 0.21/0.47  thf('27', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r1_xboole_0 @ sk_B_1 @ X0)
% 0.21/0.47          | (v1_xboole_0 @ sk_B_1)
% 0.21/0.47          | ~ (v1_xboole_0 @ (sk_C @ X0 @ sk_B_1))
% 0.21/0.47          | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['6', '26'])).
% 0.21/0.47  thf('28', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v1_xboole_0 @ X0)
% 0.21/0.47          | (r1_xboole_0 @ sk_B_1 @ (k1_tarski @ X0))
% 0.21/0.47          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.47          | (v1_xboole_0 @ sk_B_1)
% 0.21/0.47          | (r1_xboole_0 @ sk_B_1 @ (k1_tarski @ X0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['5', '27'])).
% 0.21/0.47  thf('29', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((v1_xboole_0 @ sk_B_1)
% 0.21/0.47          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.47          | (r1_xboole_0 @ sk_B_1 @ (k1_tarski @ X0))
% 0.21/0.47          | ~ (v1_xboole_0 @ X0))),
% 0.21/0.47      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.47  thf(fc5_struct_0, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.47       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.21/0.47  thf('30', plain,
% 0.21/0.47      (![X17 : $i]:
% 0.21/0.47         (~ (v1_xboole_0 @ (k2_struct_0 @ X17))
% 0.21/0.47          | ~ (l1_struct_0 @ X17)
% 0.21/0.47          | (v2_struct_0 @ X17))),
% 0.21/0.47      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.21/0.47  thf('31', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v1_xboole_0 @ X0)
% 0.21/0.47          | (r1_xboole_0 @ sk_B_1 @ (k1_tarski @ X0))
% 0.21/0.47          | (v1_xboole_0 @ sk_B_1)
% 0.21/0.47          | (v2_struct_0 @ sk_A)
% 0.21/0.47          | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.47  thf('32', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('33', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v1_xboole_0 @ X0)
% 0.21/0.47          | (r1_xboole_0 @ sk_B_1 @ (k1_tarski @ X0))
% 0.21/0.47          | (v1_xboole_0 @ sk_B_1)
% 0.21/0.47          | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.47  thf(t83_xboole_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.47  thf('34', plain,
% 0.21/0.47      (![X7 : $i, X8 : $i]:
% 0.21/0.47         (((k4_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_xboole_0 @ X7 @ X8))),
% 0.21/0.47      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.47  thf('35', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((v2_struct_0 @ sk_A)
% 0.21/0.47          | (v1_xboole_0 @ sk_B_1)
% 0.21/0.47          | ~ (v1_xboole_0 @ X0)
% 0.21/0.47          | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ X0)) = (sk_B_1)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.47  thf('36', plain,
% 0.21/0.47      (((sk_B_1)
% 0.21/0.47         != (k2_yellow19 @ sk_A @ 
% 0.21/0.47             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('37', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_B_1 @ 
% 0.21/0.47        (k1_zfmisc_1 @ 
% 0.21/0.47         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.21/0.47      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.47  thf(t14_yellow19, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.47             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.47             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.47             ( m1_subset_1 @
% 0.21/0.47               B @ 
% 0.21/0.47               ( k1_zfmisc_1 @
% 0.21/0.47                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.21/0.47           ( ( k7_subset_1 @
% 0.21/0.47               ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ 
% 0.21/0.47               ( k1_tarski @ k1_xboole_0 ) ) =
% 0.21/0.47             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.21/0.47  thf('38', plain,
% 0.21/0.47      (![X19 : $i, X20 : $i]:
% 0.21/0.47         ((v1_xboole_0 @ X19)
% 0.21/0.47          | ~ (v2_waybel_0 @ X19 @ (k3_yellow_1 @ (k2_struct_0 @ X20)))
% 0.21/0.47          | ~ (v13_waybel_0 @ X19 @ (k3_yellow_1 @ (k2_struct_0 @ X20)))
% 0.21/0.47          | ~ (m1_subset_1 @ X19 @ 
% 0.21/0.47               (k1_zfmisc_1 @ 
% 0.21/0.47                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X20)))))
% 0.21/0.47          | ((k7_subset_1 @ 
% 0.21/0.47              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X20))) @ X19 @ 
% 0.21/0.47              (k1_tarski @ k1_xboole_0))
% 0.21/0.47              = (k2_yellow19 @ X20 @ 
% 0.21/0.47                 (k3_yellow19 @ X20 @ (k2_struct_0 @ X20) @ X19)))
% 0.21/0.47          | ~ (l1_struct_0 @ X20)
% 0.21/0.47          | (v2_struct_0 @ X20))),
% 0.21/0.47      inference('cnf', [status(esa)], [t14_yellow19])).
% 0.21/0.47  thf('39', plain,
% 0.21/0.47      (![X18 : $i]: ((k3_yellow_1 @ X18) = (k3_lattice3 @ (k1_lattice3 @ X18)))),
% 0.21/0.47      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.47  thf('40', plain,
% 0.21/0.47      (![X18 : $i]: ((k3_yellow_1 @ X18) = (k3_lattice3 @ (k1_lattice3 @ X18)))),
% 0.21/0.47      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.47  thf('41', plain,
% 0.21/0.47      (![X18 : $i]: ((k3_yellow_1 @ X18) = (k3_lattice3 @ (k1_lattice3 @ X18)))),
% 0.21/0.47      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.47  thf('42', plain,
% 0.21/0.47      (![X18 : $i]: ((k3_yellow_1 @ X18) = (k3_lattice3 @ (k1_lattice3 @ X18)))),
% 0.21/0.47      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.47  thf('43', plain,
% 0.21/0.47      (![X19 : $i, X20 : $i]:
% 0.21/0.47         ((v1_xboole_0 @ X19)
% 0.21/0.47          | ~ (v2_waybel_0 @ X19 @ 
% 0.21/0.47               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X20))))
% 0.21/0.47          | ~ (v13_waybel_0 @ X19 @ 
% 0.21/0.47               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X20))))
% 0.21/0.47          | ~ (m1_subset_1 @ X19 @ 
% 0.21/0.47               (k1_zfmisc_1 @ 
% 0.21/0.47                (u1_struct_0 @ 
% 0.21/0.47                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X20))))))
% 0.21/0.47          | ((k7_subset_1 @ 
% 0.21/0.47              (u1_struct_0 @ 
% 0.21/0.47               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X20)))) @ 
% 0.21/0.47              X19 @ (k1_tarski @ k1_xboole_0))
% 0.21/0.47              = (k2_yellow19 @ X20 @ 
% 0.21/0.47                 (k3_yellow19 @ X20 @ (k2_struct_0 @ X20) @ X19)))
% 0.21/0.47          | ~ (l1_struct_0 @ X20)
% 0.21/0.47          | (v2_struct_0 @ X20))),
% 0.21/0.47      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 0.21/0.47  thf('44', plain,
% 0.21/0.47      (((v2_struct_0 @ sk_A)
% 0.21/0.47        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.47        | ((k7_subset_1 @ 
% 0.21/0.47            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.21/0.47            sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.21/0.47            = (k2_yellow19 @ sk_A @ 
% 0.21/0.47               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.21/0.47        | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.21/0.47             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.21/0.47        | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.21/0.47             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.21/0.47        | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['37', '43'])).
% 0.21/0.47  thf('45', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('46', plain,
% 0.21/0.47      ((v13_waybel_0 @ sk_B_1 @ 
% 0.21/0.47        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.47      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.47  thf('47', plain,
% 0.21/0.47      ((v2_waybel_0 @ sk_B_1 @ 
% 0.21/0.47        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.47      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.47  thf('48', plain,
% 0.21/0.47      (((v2_struct_0 @ sk_A)
% 0.21/0.47        | ((k7_subset_1 @ 
% 0.21/0.47            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.21/0.47            sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.21/0.47            = (k2_yellow19 @ sk_A @ 
% 0.21/0.47               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.21/0.47        | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.47      inference('demod', [status(thm)], ['44', '45', '46', '47'])).
% 0.21/0.47  thf('49', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_B_1 @ 
% 0.21/0.47        (k1_zfmisc_1 @ 
% 0.21/0.47         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.21/0.47      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.47  thf(redefinition_k7_subset_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.47       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.21/0.47  thf('50', plain,
% 0.21/0.47      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.21/0.47          | ((k7_subset_1 @ X15 @ X14 @ X16) = (k4_xboole_0 @ X14 @ X16)))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.21/0.47  thf('51', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((k7_subset_1 @ 
% 0.21/0.47           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.21/0.47           sk_B_1 @ X0) = (k4_xboole_0 @ sk_B_1 @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.47  thf('52', plain,
% 0.21/0.47      (((v2_struct_0 @ sk_A)
% 0.21/0.47        | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.21/0.47            = (k2_yellow19 @ sk_A @ 
% 0.21/0.47               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.21/0.47        | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.47      inference('demod', [status(thm)], ['48', '51'])).
% 0.21/0.47  thf('53', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('54', plain,
% 0.21/0.47      (((v1_xboole_0 @ sk_B_1)
% 0.21/0.47        | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.21/0.47            = (k2_yellow19 @ sk_A @ 
% 0.21/0.47               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))),
% 0.21/0.47      inference('clc', [status(thm)], ['52', '53'])).
% 0.21/0.47  thf('55', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('56', plain,
% 0.21/0.47      (((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.21/0.47         = (k2_yellow19 @ sk_A @ 
% 0.21/0.47            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.21/0.47      inference('clc', [status(thm)], ['54', '55'])).
% 0.21/0.47  thf('57', plain,
% 0.21/0.47      (((sk_B_1) != (k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0)))),
% 0.21/0.47      inference('demod', [status(thm)], ['36', '56'])).
% 0.21/0.47  thf('58', plain,
% 0.21/0.47      ((((sk_B_1) != (sk_B_1))
% 0.21/0.47        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.47        | (v1_xboole_0 @ sk_B_1)
% 0.21/0.47        | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['35', '57'])).
% 0.21/0.47  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.47  thf('59', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.47      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.47  thf('60', plain,
% 0.21/0.47      ((((sk_B_1) != (sk_B_1)) | (v1_xboole_0 @ sk_B_1) | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['58', '59'])).
% 0.21/0.47  thf('61', plain, (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ sk_B_1))),
% 0.21/0.47      inference('simplify', [status(thm)], ['60'])).
% 0.21/0.47  thf('62', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('63', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.21/0.47      inference('clc', [status(thm)], ['61', '62'])).
% 0.21/0.47  thf('64', plain, ($false), inference('demod', [status(thm)], ['0', '63'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
