%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cOVkub4u1R

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 182 expanded)
%              Number of leaves         :   43 (  77 expanded)
%              Depth                    :   18
%              Number of atoms          :  914 (2231 expanded)
%              Number of equality atoms :   49 ( 100 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X13 ) @ X14 )
      | ( r2_hidden @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t1_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X18: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X18 ) @ X18 ) ) ),
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

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('11',plain,(
    ! [X12: $i] :
      ( r1_xboole_0 @ X12 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('12',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('13',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X18: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X18 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t1_mcart_1])).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('22',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','23'])).

thf('25',plain,(
    sk_B_3
 != ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('27',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('28',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
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
    ! [X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( v2_waybel_0 @ X28 @ ( k3_yellow_1 @ ( k2_struct_0 @ X29 ) ) )
      | ~ ( v13_waybel_0 @ X28 @ ( k3_yellow_1 @ ( k2_struct_0 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X29 ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X29 ) ) ) @ X28 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X29 @ ( k3_yellow19 @ X29 @ ( k2_struct_0 @ X29 ) @ X28 ) ) )
      | ~ ( l1_struct_0 @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow19])).

thf('30',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('31',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('32',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('33',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('34',plain,(
    ! [X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( v2_waybel_0 @ X28 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X29 ) ) ) )
      | ~ ( v13_waybel_0 @ X28 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X29 ) ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X29 ) ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X29 ) ) ) ) @ X28 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X29 @ ( k3_yellow19 @ X29 @ ( k2_struct_0 @ X29 ) @ X28 ) ) )
      | ~ ( l1_struct_0 @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(demod,[status(thm)],['29','30','31','32','33'])).

thf('35',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_3 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) ) )
    | ~ ( v13_waybel_0 @ sk_B_3 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B_3 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['28','34'])).

thf('36',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('38',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k7_subset_1 @ X16 @ X15 @ X17 )
        = ( k4_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_3 @ X0 )
      = ( k4_xboole_0 @ sk_B_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v13_waybel_0 @ sk_B_3 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('42',plain,(
    v13_waybel_0 @ sk_B_3 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    v2_waybel_0 @ sk_B_3 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('45',plain,(
    v2_waybel_0 @ sk_B_3 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_xboole_0 @ sk_B_3 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) ) )
    | ( v1_xboole_0 @ sk_B_3 ) ),
    inference(demod,[status(thm)],['35','36','39','42','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v1_xboole_0 @ sk_B_3 )
    | ( ( k4_xboole_0 @ sk_B_3 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v1_xboole_0 @ sk_B_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k4_xboole_0 @ sk_B_3 @ ( k1_tarski @ k1_xboole_0 ) )
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_3 ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    sk_B_3
 != ( k4_xboole_0 @ sk_B_3 @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['25','50'])).

thf('52',plain,
    ( ( sk_B_3 != sk_B_3 )
    | ( r2_hidden @ k1_xboole_0 @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['24','51'])).

thf('53',plain,(
    r2_hidden @ k1_xboole_0 @ sk_B_3 ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( v1_subset_1 @ X30 @ ( u1_struct_0 @ ( k3_yellow_1 @ X31 ) ) )
      | ~ ( v2_waybel_0 @ X30 @ ( k3_yellow_1 @ X31 ) )
      | ~ ( v13_waybel_0 @ X30 @ ( k3_yellow_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X31 ) ) ) )
      | ~ ( r2_hidden @ X32 @ X30 )
      | ~ ( v1_xboole_0 @ X32 )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t2_yellow19])).

thf('56',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('57',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('58',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('59',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('60',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( v1_subset_1 @ X30 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X31 ) ) ) )
      | ~ ( v2_waybel_0 @ X30 @ ( k3_lattice3 @ ( k1_lattice3 @ X31 ) ) )
      | ~ ( v13_waybel_0 @ X30 @ ( k3_lattice3 @ ( k1_lattice3 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X31 ) ) ) ) )
      | ~ ( r2_hidden @ X32 @ X30 )
      | ~ ( v1_xboole_0 @ X32 )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(demod,[status(thm)],['55','56','57','58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_3 )
      | ~ ( v13_waybel_0 @ sk_B_3 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_3 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['54','60'])).

thf('62',plain,(
    v13_waybel_0 @ sk_B_3 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('63',plain,(
    v2_waybel_0 @ sk_B_3 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('64',plain,(
    v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('66',plain,(
    v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_3 )
      | ( v1_xboole_0 @ sk_B_3 ) ) ),
    inference(demod,[status(thm)],['61','62','63','66'])).

thf('68',plain,
    ( ( v1_xboole_0 @ sk_B_3 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','67'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('69',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('70',plain,
    ( ( v1_xboole_0 @ sk_B_3 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( v1_xboole_0 @ sk_B_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','72'])).

thf('74',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['73','74'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('76',plain,(
    ! [X26: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    $false ),
    inference(demod,[status(thm)],['0','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cOVkub4u1R
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:49:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.57  % Solved by: fo/fo7.sh
% 0.20/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.57  % done 175 iterations in 0.083s
% 0.20/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.57  % SZS output start Refutation
% 0.20/0.57  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.20/0.57  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.57  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.20/0.57  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.20/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.57  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.20/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.57  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.20/0.57  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.20/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.57  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.57  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.20/0.57  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.20/0.57  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.20/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.57  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.57  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.20/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.57  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.20/0.57  thf(sk_B_3_type, type, sk_B_3: $i).
% 0.20/0.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.57  thf(t15_yellow19, conjecture,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.57       ( ![B:$i]:
% 0.20/0.57         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.57             ( v1_subset_1 @
% 0.20/0.57               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.20/0.57             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.20/0.57             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.20/0.57             ( m1_subset_1 @
% 0.20/0.57               B @ 
% 0.20/0.57               ( k1_zfmisc_1 @
% 0.20/0.57                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.20/0.57           ( ( B ) =
% 0.20/0.57             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.20/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.57    (~( ![A:$i]:
% 0.20/0.57        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.57          ( ![B:$i]:
% 0.20/0.57            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.57                ( v1_subset_1 @
% 0.20/0.57                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.20/0.57                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.20/0.57                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.20/0.57                ( m1_subset_1 @
% 0.20/0.57                  B @ 
% 0.20/0.57                  ( k1_zfmisc_1 @
% 0.20/0.57                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.20/0.57              ( ( B ) =
% 0.20/0.57                ( k2_yellow19 @
% 0.20/0.57                  A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.20/0.57    inference('cnf.neg', [status(esa)], [t15_yellow19])).
% 0.20/0.57  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(d3_struct_0, axiom,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.20/0.57  thf('1', plain,
% 0.20/0.57      (![X25 : $i]:
% 0.20/0.57         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.20/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.57  thf(l27_zfmisc_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.20/0.57  thf('2', plain,
% 0.20/0.57      (![X13 : $i, X14 : $i]:
% 0.20/0.57         ((r1_xboole_0 @ (k1_tarski @ X13) @ X14) | (r2_hidden @ X13 @ X14))),
% 0.20/0.57      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.20/0.57  thf(t1_mcart_1, axiom,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.57          ( ![B:$i]: ( ~( ( r2_hidden @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) ) ))).
% 0.20/0.57  thf('3', plain,
% 0.20/0.57      (![X18 : $i]:
% 0.20/0.57         (((X18) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X18) @ X18))),
% 0.20/0.57      inference('cnf', [status(esa)], [t1_mcart_1])).
% 0.20/0.57  thf(t4_xboole_0, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.57            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.57       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.57            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.57  thf('4', plain,
% 0.20/0.57      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.20/0.57         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.20/0.57          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.20/0.57      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.57  thf('5', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.57  thf('6', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((r2_hidden @ X1 @ X0)
% 0.20/0.57          | ((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['2', '5'])).
% 0.20/0.57  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.57  thf('7', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.57  thf(t100_xboole_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.57  thf('8', plain,
% 0.20/0.57      (![X9 : $i, X10 : $i]:
% 0.20/0.57         ((k4_xboole_0 @ X9 @ X10)
% 0.20/0.57           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.20/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.57  thf('9', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((k4_xboole_0 @ X0 @ X1)
% 0.20/0.57           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.57      inference('sup+', [status(thm)], ['7', '8'])).
% 0.20/0.57  thf('10', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         (((k4_xboole_0 @ X0 @ (k1_tarski @ X1))
% 0.20/0.57            = (k5_xboole_0 @ X0 @ k1_xboole_0))
% 0.20/0.57          | (r2_hidden @ X1 @ X0))),
% 0.20/0.57      inference('sup+', [status(thm)], ['6', '9'])).
% 0.20/0.57  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.57  thf('11', plain, (![X12 : $i]: (r1_xboole_0 @ X12 @ k1_xboole_0)),
% 0.20/0.57      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.57  thf(d1_xboole_0, axiom,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.57  thf('12', plain,
% 0.20/0.57      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.20/0.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.57  thf('13', plain,
% 0.20/0.57      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.20/0.57         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.20/0.57          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.20/0.57      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.57  thf('14', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.57  thf('15', plain,
% 0.20/0.57      (![X0 : $i]: (v1_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['11', '14'])).
% 0.20/0.57  thf('16', plain,
% 0.20/0.57      (![X18 : $i]:
% 0.20/0.57         (((X18) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X18) @ X18))),
% 0.20/0.57      inference('cnf', [status(esa)], [t1_mcart_1])).
% 0.20/0.57  thf('17', plain,
% 0.20/0.57      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.20/0.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.57  thf('18', plain,
% 0.20/0.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.57  thf('19', plain,
% 0.20/0.57      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['15', '18'])).
% 0.20/0.57  thf('20', plain,
% 0.20/0.57      (![X9 : $i, X10 : $i]:
% 0.20/0.57         ((k4_xboole_0 @ X9 @ X10)
% 0.20/0.57           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.20/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.57  thf('21', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.57      inference('sup+', [status(thm)], ['19', '20'])).
% 0.20/0.57  thf(t3_boole, axiom,
% 0.20/0.57    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.57  thf('22', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.20/0.57      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.57  thf('23', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.57      inference('sup+', [status(thm)], ['21', '22'])).
% 0.20/0.57  thf('24', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         (((k4_xboole_0 @ X0 @ (k1_tarski @ X1)) = (X0))
% 0.20/0.57          | (r2_hidden @ X1 @ X0))),
% 0.20/0.57      inference('demod', [status(thm)], ['10', '23'])).
% 0.20/0.57  thf('25', plain,
% 0.20/0.57      (((sk_B_3)
% 0.20/0.57         != (k2_yellow19 @ sk_A @ 
% 0.20/0.57             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('26', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_B_3 @ 
% 0.20/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(d2_yellow_1, axiom,
% 0.20/0.57    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.20/0.57  thf('27', plain,
% 0.20/0.57      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.57  thf('28', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_B_3 @ 
% 0.20/0.57        (k1_zfmisc_1 @ 
% 0.20/0.57         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.20/0.57      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.57  thf(t14_yellow19, axiom,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.57       ( ![B:$i]:
% 0.20/0.57         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.57             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.20/0.57             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.20/0.57             ( m1_subset_1 @
% 0.20/0.57               B @ 
% 0.20/0.57               ( k1_zfmisc_1 @
% 0.20/0.57                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.20/0.57           ( ( k7_subset_1 @
% 0.20/0.57               ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ 
% 0.20/0.57               ( k1_tarski @ k1_xboole_0 ) ) =
% 0.20/0.57             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.20/0.57  thf('29', plain,
% 0.20/0.57      (![X28 : $i, X29 : $i]:
% 0.20/0.57         ((v1_xboole_0 @ X28)
% 0.20/0.57          | ~ (v2_waybel_0 @ X28 @ (k3_yellow_1 @ (k2_struct_0 @ X29)))
% 0.20/0.57          | ~ (v13_waybel_0 @ X28 @ (k3_yellow_1 @ (k2_struct_0 @ X29)))
% 0.20/0.57          | ~ (m1_subset_1 @ X28 @ 
% 0.20/0.57               (k1_zfmisc_1 @ 
% 0.20/0.57                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X29)))))
% 0.20/0.57          | ((k7_subset_1 @ 
% 0.20/0.57              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X29))) @ X28 @ 
% 0.20/0.57              (k1_tarski @ k1_xboole_0))
% 0.20/0.57              = (k2_yellow19 @ X29 @ 
% 0.20/0.57                 (k3_yellow19 @ X29 @ (k2_struct_0 @ X29) @ X28)))
% 0.20/0.57          | ~ (l1_struct_0 @ X29)
% 0.20/0.57          | (v2_struct_0 @ X29))),
% 0.20/0.57      inference('cnf', [status(esa)], [t14_yellow19])).
% 0.20/0.57  thf('30', plain,
% 0.20/0.57      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.57  thf('31', plain,
% 0.20/0.57      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.57  thf('32', plain,
% 0.20/0.57      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.57  thf('33', plain,
% 0.20/0.57      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.57  thf('34', plain,
% 0.20/0.57      (![X28 : $i, X29 : $i]:
% 0.20/0.57         ((v1_xboole_0 @ X28)
% 0.20/0.57          | ~ (v2_waybel_0 @ X28 @ 
% 0.20/0.57               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X29))))
% 0.20/0.57          | ~ (v13_waybel_0 @ X28 @ 
% 0.20/0.57               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X29))))
% 0.20/0.57          | ~ (m1_subset_1 @ X28 @ 
% 0.20/0.57               (k1_zfmisc_1 @ 
% 0.20/0.57                (u1_struct_0 @ 
% 0.20/0.57                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X29))))))
% 0.20/0.57          | ((k7_subset_1 @ 
% 0.20/0.57              (u1_struct_0 @ 
% 0.20/0.57               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X29)))) @ 
% 0.20/0.57              X28 @ (k1_tarski @ k1_xboole_0))
% 0.20/0.57              = (k2_yellow19 @ X29 @ 
% 0.20/0.57                 (k3_yellow19 @ X29 @ (k2_struct_0 @ X29) @ X28)))
% 0.20/0.57          | ~ (l1_struct_0 @ X29)
% 0.20/0.57          | (v2_struct_0 @ X29))),
% 0.20/0.57      inference('demod', [status(thm)], ['29', '30', '31', '32', '33'])).
% 0.20/0.57  thf('35', plain,
% 0.20/0.57      (((v2_struct_0 @ sk_A)
% 0.20/0.57        | ~ (l1_struct_0 @ sk_A)
% 0.20/0.57        | ((k7_subset_1 @ 
% 0.20/0.57            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.20/0.57            sk_B_3 @ (k1_tarski @ k1_xboole_0))
% 0.20/0.57            = (k2_yellow19 @ sk_A @ 
% 0.20/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3)))
% 0.20/0.57        | ~ (v13_waybel_0 @ sk_B_3 @ 
% 0.20/0.57             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.20/0.57        | ~ (v2_waybel_0 @ sk_B_3 @ 
% 0.20/0.57             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.20/0.57        | (v1_xboole_0 @ sk_B_3))),
% 0.20/0.57      inference('sup-', [status(thm)], ['28', '34'])).
% 0.20/0.57  thf('36', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('37', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_B_3 @ 
% 0.20/0.57        (k1_zfmisc_1 @ 
% 0.20/0.57         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.20/0.57      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.57  thf(redefinition_k7_subset_1, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i]:
% 0.20/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.57       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.20/0.57  thf('38', plain,
% 0.20/0.57      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.20/0.57          | ((k7_subset_1 @ X16 @ X15 @ X17) = (k4_xboole_0 @ X15 @ X17)))),
% 0.20/0.57      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.20/0.57  thf('39', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((k7_subset_1 @ 
% 0.20/0.57           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.20/0.57           sk_B_3 @ X0) = (k4_xboole_0 @ sk_B_3 @ X0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.57  thf('40', plain,
% 0.20/0.57      ((v13_waybel_0 @ sk_B_3 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('41', plain,
% 0.20/0.57      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.57  thf('42', plain,
% 0.20/0.57      ((v13_waybel_0 @ sk_B_3 @ 
% 0.20/0.57        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.20/0.57      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.57  thf('43', plain,
% 0.20/0.57      ((v2_waybel_0 @ sk_B_3 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('44', plain,
% 0.20/0.57      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.57  thf('45', plain,
% 0.20/0.57      ((v2_waybel_0 @ sk_B_3 @ 
% 0.20/0.57        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.20/0.57      inference('demod', [status(thm)], ['43', '44'])).
% 0.20/0.57  thf('46', plain,
% 0.20/0.57      (((v2_struct_0 @ sk_A)
% 0.20/0.57        | ((k4_xboole_0 @ sk_B_3 @ (k1_tarski @ k1_xboole_0))
% 0.20/0.57            = (k2_yellow19 @ sk_A @ 
% 0.20/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3)))
% 0.20/0.57        | (v1_xboole_0 @ sk_B_3))),
% 0.20/0.57      inference('demod', [status(thm)], ['35', '36', '39', '42', '45'])).
% 0.20/0.57  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('48', plain,
% 0.20/0.57      (((v1_xboole_0 @ sk_B_3)
% 0.20/0.57        | ((k4_xboole_0 @ sk_B_3 @ (k1_tarski @ k1_xboole_0))
% 0.20/0.57            = (k2_yellow19 @ sk_A @ 
% 0.20/0.57               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3))))),
% 0.20/0.57      inference('clc', [status(thm)], ['46', '47'])).
% 0.20/0.57  thf('49', plain, (~ (v1_xboole_0 @ sk_B_3)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('50', plain,
% 0.20/0.57      (((k4_xboole_0 @ sk_B_3 @ (k1_tarski @ k1_xboole_0))
% 0.20/0.57         = (k2_yellow19 @ sk_A @ 
% 0.20/0.57            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_3)))),
% 0.20/0.57      inference('clc', [status(thm)], ['48', '49'])).
% 0.20/0.57  thf('51', plain,
% 0.20/0.57      (((sk_B_3) != (k4_xboole_0 @ sk_B_3 @ (k1_tarski @ k1_xboole_0)))),
% 0.20/0.57      inference('demod', [status(thm)], ['25', '50'])).
% 0.20/0.57  thf('52', plain,
% 0.20/0.57      ((((sk_B_3) != (sk_B_3)) | (r2_hidden @ k1_xboole_0 @ sk_B_3))),
% 0.20/0.57      inference('sup-', [status(thm)], ['24', '51'])).
% 0.20/0.57  thf('53', plain, ((r2_hidden @ k1_xboole_0 @ sk_B_3)),
% 0.20/0.57      inference('simplify', [status(thm)], ['52'])).
% 0.20/0.57  thf('54', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_B_3 @ 
% 0.20/0.57        (k1_zfmisc_1 @ 
% 0.20/0.57         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.20/0.57      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.57  thf(t2_yellow19, axiom,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.57       ( ![B:$i]:
% 0.20/0.57         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.57             ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 0.20/0.57             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.20/0.57             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.20/0.57             ( m1_subset_1 @
% 0.20/0.57               B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 0.20/0.57           ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ))).
% 0.20/0.57  thf('55', plain,
% 0.20/0.57      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.20/0.57         ((v1_xboole_0 @ X30)
% 0.20/0.57          | ~ (v1_subset_1 @ X30 @ (u1_struct_0 @ (k3_yellow_1 @ X31)))
% 0.20/0.57          | ~ (v2_waybel_0 @ X30 @ (k3_yellow_1 @ X31))
% 0.20/0.57          | ~ (v13_waybel_0 @ X30 @ (k3_yellow_1 @ X31))
% 0.20/0.57          | ~ (m1_subset_1 @ X30 @ 
% 0.20/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X31))))
% 0.20/0.57          | ~ (r2_hidden @ X32 @ X30)
% 0.20/0.57          | ~ (v1_xboole_0 @ X32)
% 0.20/0.57          | (v1_xboole_0 @ X31))),
% 0.20/0.57      inference('cnf', [status(esa)], [t2_yellow19])).
% 0.20/0.57  thf('56', plain,
% 0.20/0.57      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.57  thf('57', plain,
% 0.20/0.57      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.57  thf('58', plain,
% 0.20/0.57      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.57  thf('59', plain,
% 0.20/0.57      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.57  thf('60', plain,
% 0.20/0.57      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.20/0.57         ((v1_xboole_0 @ X30)
% 0.20/0.57          | ~ (v1_subset_1 @ X30 @ 
% 0.20/0.57               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X31))))
% 0.20/0.57          | ~ (v2_waybel_0 @ X30 @ (k3_lattice3 @ (k1_lattice3 @ X31)))
% 0.20/0.57          | ~ (v13_waybel_0 @ X30 @ (k3_lattice3 @ (k1_lattice3 @ X31)))
% 0.20/0.57          | ~ (m1_subset_1 @ X30 @ 
% 0.20/0.57               (k1_zfmisc_1 @ 
% 0.20/0.57                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X31)))))
% 0.20/0.57          | ~ (r2_hidden @ X32 @ X30)
% 0.20/0.57          | ~ (v1_xboole_0 @ X32)
% 0.20/0.57          | (v1_xboole_0 @ X31))),
% 0.20/0.57      inference('demod', [status(thm)], ['55', '56', '57', '58', '59'])).
% 0.20/0.57  thf('61', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57          | ~ (v1_xboole_0 @ X0)
% 0.20/0.57          | ~ (r2_hidden @ X0 @ sk_B_3)
% 0.20/0.57          | ~ (v13_waybel_0 @ sk_B_3 @ 
% 0.20/0.57               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.20/0.57          | ~ (v2_waybel_0 @ sk_B_3 @ 
% 0.20/0.57               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.20/0.57          | ~ (v1_subset_1 @ sk_B_3 @ 
% 0.20/0.57               (u1_struct_0 @ 
% 0.20/0.57                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.20/0.57          | (v1_xboole_0 @ sk_B_3))),
% 0.20/0.57      inference('sup-', [status(thm)], ['54', '60'])).
% 0.20/0.57  thf('62', plain,
% 0.20/0.57      ((v13_waybel_0 @ sk_B_3 @ 
% 0.20/0.57        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.20/0.57      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.57  thf('63', plain,
% 0.20/0.57      ((v2_waybel_0 @ sk_B_3 @ 
% 0.20/0.57        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.20/0.57      inference('demod', [status(thm)], ['43', '44'])).
% 0.20/0.57  thf('64', plain,
% 0.20/0.57      ((v1_subset_1 @ sk_B_3 @ 
% 0.20/0.57        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('65', plain,
% 0.20/0.57      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.20/0.57      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.20/0.57  thf('66', plain,
% 0.20/0.57      ((v1_subset_1 @ sk_B_3 @ 
% 0.20/0.57        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.20/0.57      inference('demod', [status(thm)], ['64', '65'])).
% 0.20/0.57  thf('67', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.57          | ~ (v1_xboole_0 @ X0)
% 0.20/0.57          | ~ (r2_hidden @ X0 @ sk_B_3)
% 0.20/0.57          | (v1_xboole_0 @ sk_B_3))),
% 0.20/0.57      inference('demod', [status(thm)], ['61', '62', '63', '66'])).
% 0.20/0.57  thf('68', plain,
% 0.20/0.57      (((v1_xboole_0 @ sk_B_3)
% 0.20/0.57        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.57        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['53', '67'])).
% 0.20/0.57  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.57  thf('69', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.57  thf('70', plain,
% 0.20/0.57      (((v1_xboole_0 @ sk_B_3) | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.20/0.57      inference('demod', [status(thm)], ['68', '69'])).
% 0.20/0.57  thf('71', plain, (~ (v1_xboole_0 @ sk_B_3)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('72', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 0.20/0.57      inference('clc', [status(thm)], ['70', '71'])).
% 0.20/0.57  thf('73', plain,
% 0.20/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.57      inference('sup+', [status(thm)], ['1', '72'])).
% 0.20/0.57  thf('74', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('75', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.20/0.57      inference('demod', [status(thm)], ['73', '74'])).
% 0.20/0.57  thf(fc2_struct_0, axiom,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.57       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.57  thf('76', plain,
% 0.20/0.57      (![X26 : $i]:
% 0.20/0.57         (~ (v1_xboole_0 @ (u1_struct_0 @ X26))
% 0.20/0.57          | ~ (l1_struct_0 @ X26)
% 0.20/0.57          | (v2_struct_0 @ X26))),
% 0.20/0.57      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.57  thf('77', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.57      inference('sup-', [status(thm)], ['75', '76'])).
% 0.20/0.57  thf('78', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('79', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.57      inference('demod', [status(thm)], ['77', '78'])).
% 0.20/0.57  thf('80', plain, ($false), inference('demod', [status(thm)], ['0', '79'])).
% 0.20/0.57  
% 0.20/0.57  % SZS output end Refutation
% 0.20/0.57  
% 0.20/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
