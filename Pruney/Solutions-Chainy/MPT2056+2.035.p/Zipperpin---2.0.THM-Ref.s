%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.G5GzYfmDCD

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:45 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 159 expanded)
%              Number of leaves         :   38 (  68 expanded)
%              Depth                    :   18
%              Number of atoms          :  786 (2064 expanded)
%              Number of equality atoms :   36 (  85 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k4_xboole_0 @ X16 @ ( k1_tarski @ X17 ) )
        = X16 )
      | ( r2_hidden @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('3',plain,(
    sk_B_1
 != ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('5',plain,(
    ! [X23: $i] :
      ( ( k3_yellow_1 @ X23 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('6',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
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
    ! [X24: $i,X25: $i] :
      ( ( v1_xboole_0 @ X24 )
      | ~ ( v2_waybel_0 @ X24 @ ( k3_yellow_1 @ ( k2_struct_0 @ X25 ) ) )
      | ~ ( v13_waybel_0 @ X24 @ ( k3_yellow_1 @ ( k2_struct_0 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X25 ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X25 ) ) ) @ X24 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X25 @ ( k3_yellow19 @ X25 @ ( k2_struct_0 @ X25 ) @ X24 ) ) )
      | ~ ( l1_struct_0 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow19])).

thf('8',plain,(
    ! [X23: $i] :
      ( ( k3_yellow_1 @ X23 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('9',plain,(
    ! [X23: $i] :
      ( ( k3_yellow_1 @ X23 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('10',plain,(
    ! [X23: $i] :
      ( ( k3_yellow_1 @ X23 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('11',plain,(
    ! [X23: $i] :
      ( ( k3_yellow_1 @ X23 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('12',plain,(
    ! [X24: $i,X25: $i] :
      ( ( v1_xboole_0 @ X24 )
      | ~ ( v2_waybel_0 @ X24 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X25 ) ) ) )
      | ~ ( v13_waybel_0 @ X24 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X25 ) ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X25 ) ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X25 ) ) ) ) @ X24 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X25 @ ( k3_yellow19 @ X25 @ ( k2_struct_0 @ X25 ) @ X24 ) ) )
      | ~ ( l1_struct_0 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(demod,[status(thm)],['7','8','9','10','11'])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf('14',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k7_subset_1 @ X19 @ X18 @ X20 )
        = ( k4_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_1 @ X0 )
      = ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X23: $i] :
      ( ( k3_yellow_1 @ X23 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('20',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X23: $i] :
      ( ( k3_yellow_1 @ X23 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('23',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14','17','20','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    sk_B_1
 != ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['3','28'])).

thf('30',plain,
    ( ( sk_B_1 != sk_B_1 )
    | ( r2_hidden @ k1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['2','29'])).

thf('31',plain,(
    r2_hidden @ k1_xboole_0 @ sk_B_1 ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
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

thf('33',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( v1_subset_1 @ X26 @ ( u1_struct_0 @ ( k3_yellow_1 @ X27 ) ) )
      | ~ ( v2_waybel_0 @ X26 @ ( k3_yellow_1 @ X27 ) )
      | ~ ( v13_waybel_0 @ X26 @ ( k3_yellow_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X27 ) ) ) )
      | ~ ( r2_hidden @ X28 @ X26 )
      | ~ ( v1_xboole_0 @ X28 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t2_yellow19])).

thf('34',plain,(
    ! [X23: $i] :
      ( ( k3_yellow_1 @ X23 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('35',plain,(
    ! [X23: $i] :
      ( ( k3_yellow_1 @ X23 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('36',plain,(
    ! [X23: $i] :
      ( ( k3_yellow_1 @ X23 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('37',plain,(
    ! [X23: $i] :
      ( ( k3_yellow_1 @ X23 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('38',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( v1_subset_1 @ X26 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) )
      | ~ ( v2_waybel_0 @ X26 @ ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) )
      | ~ ( v13_waybel_0 @ X26 @ ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ) )
      | ~ ( r2_hidden @ X28 @ X26 )
      | ~ ( v1_xboole_0 @ X28 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(demod,[status(thm)],['33','34','35','36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['32','38'])).

thf('40',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('41',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('42',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X23: $i] :
      ( ( k3_yellow_1 @ X23 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('44',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['39','40','41','44'])).

thf('46',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','45'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('47',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('48',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('49',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('51',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('52',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','53'])).

thf('55',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['47','54'])).

thf('56',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','55'])).

thf('57',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','58'])).

thf('60',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('62',plain,(
    ! [X22: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('63',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    $false ),
    inference(demod,[status(thm)],['0','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.G5GzYfmDCD
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:34:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 79 iterations in 0.036s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.22/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.48  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.22/0.48  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.22/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.48  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.22/0.48  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.22/0.48  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.22/0.48  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.22/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.48  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.22/0.48  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.22/0.48  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.48  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(t15_yellow19, conjecture,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.22/0.48             ( v1_subset_1 @
% 0.22/0.48               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.22/0.48             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.22/0.48             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.22/0.48             ( m1_subset_1 @
% 0.22/0.48               B @ 
% 0.22/0.48               ( k1_zfmisc_1 @
% 0.22/0.48                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.22/0.48           ( ( B ) =
% 0.22/0.48             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i]:
% 0.22/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.48          ( ![B:$i]:
% 0.22/0.48            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.22/0.48                ( v1_subset_1 @
% 0.22/0.48                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.22/0.48                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.22/0.48                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.22/0.48                ( m1_subset_1 @
% 0.22/0.48                  B @ 
% 0.22/0.48                  ( k1_zfmisc_1 @
% 0.22/0.48                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.22/0.48              ( ( B ) =
% 0.22/0.48                ( k2_yellow19 @
% 0.22/0.48                  A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t15_yellow19])).
% 0.22/0.48  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(d3_struct_0, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.22/0.48  thf('1', plain,
% 0.22/0.48      (![X21 : $i]:
% 0.22/0.48         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.22/0.48      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.48  thf(t65_zfmisc_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.22/0.48       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.22/0.48  thf('2', plain,
% 0.22/0.48      (![X16 : $i, X17 : $i]:
% 0.22/0.48         (((k4_xboole_0 @ X16 @ (k1_tarski @ X17)) = (X16))
% 0.22/0.48          | (r2_hidden @ X17 @ X16))),
% 0.22/0.48      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.22/0.48  thf('3', plain,
% 0.22/0.48      (((sk_B_1)
% 0.22/0.48         != (k2_yellow19 @ sk_A @ 
% 0.22/0.48             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('4', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_B_1 @ 
% 0.22/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(d2_yellow_1, axiom,
% 0.22/0.48    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.22/0.48  thf('5', plain,
% 0.22/0.48      (![X23 : $i]: ((k3_yellow_1 @ X23) = (k3_lattice3 @ (k1_lattice3 @ X23)))),
% 0.22/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.22/0.48  thf('6', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_B_1 @ 
% 0.22/0.48        (k1_zfmisc_1 @ 
% 0.22/0.48         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.22/0.48      inference('demod', [status(thm)], ['4', '5'])).
% 0.22/0.48  thf(t14_yellow19, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.22/0.48             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.22/0.48             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.22/0.48             ( m1_subset_1 @
% 0.22/0.48               B @ 
% 0.22/0.48               ( k1_zfmisc_1 @
% 0.22/0.48                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.22/0.48           ( ( k7_subset_1 @
% 0.22/0.48               ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ 
% 0.22/0.48               ( k1_tarski @ k1_xboole_0 ) ) =
% 0.22/0.48             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.22/0.48  thf('7', plain,
% 0.22/0.48      (![X24 : $i, X25 : $i]:
% 0.22/0.48         ((v1_xboole_0 @ X24)
% 0.22/0.48          | ~ (v2_waybel_0 @ X24 @ (k3_yellow_1 @ (k2_struct_0 @ X25)))
% 0.22/0.48          | ~ (v13_waybel_0 @ X24 @ (k3_yellow_1 @ (k2_struct_0 @ X25)))
% 0.22/0.48          | ~ (m1_subset_1 @ X24 @ 
% 0.22/0.48               (k1_zfmisc_1 @ 
% 0.22/0.48                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X25)))))
% 0.22/0.48          | ((k7_subset_1 @ 
% 0.22/0.48              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X25))) @ X24 @ 
% 0.22/0.48              (k1_tarski @ k1_xboole_0))
% 0.22/0.48              = (k2_yellow19 @ X25 @ 
% 0.22/0.48                 (k3_yellow19 @ X25 @ (k2_struct_0 @ X25) @ X24)))
% 0.22/0.48          | ~ (l1_struct_0 @ X25)
% 0.22/0.48          | (v2_struct_0 @ X25))),
% 0.22/0.48      inference('cnf', [status(esa)], [t14_yellow19])).
% 0.22/0.48  thf('8', plain,
% 0.22/0.48      (![X23 : $i]: ((k3_yellow_1 @ X23) = (k3_lattice3 @ (k1_lattice3 @ X23)))),
% 0.22/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.22/0.48  thf('9', plain,
% 0.22/0.48      (![X23 : $i]: ((k3_yellow_1 @ X23) = (k3_lattice3 @ (k1_lattice3 @ X23)))),
% 0.22/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.22/0.48  thf('10', plain,
% 0.22/0.48      (![X23 : $i]: ((k3_yellow_1 @ X23) = (k3_lattice3 @ (k1_lattice3 @ X23)))),
% 0.22/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.22/0.48  thf('11', plain,
% 0.22/0.48      (![X23 : $i]: ((k3_yellow_1 @ X23) = (k3_lattice3 @ (k1_lattice3 @ X23)))),
% 0.22/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.22/0.48  thf('12', plain,
% 0.22/0.48      (![X24 : $i, X25 : $i]:
% 0.22/0.48         ((v1_xboole_0 @ X24)
% 0.22/0.48          | ~ (v2_waybel_0 @ X24 @ 
% 0.22/0.48               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X25))))
% 0.22/0.48          | ~ (v13_waybel_0 @ X24 @ 
% 0.22/0.48               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X25))))
% 0.22/0.48          | ~ (m1_subset_1 @ X24 @ 
% 0.22/0.48               (k1_zfmisc_1 @ 
% 0.22/0.48                (u1_struct_0 @ 
% 0.22/0.48                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X25))))))
% 0.22/0.48          | ((k7_subset_1 @ 
% 0.22/0.48              (u1_struct_0 @ 
% 0.22/0.48               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X25)))) @ 
% 0.22/0.48              X24 @ (k1_tarski @ k1_xboole_0))
% 0.22/0.48              = (k2_yellow19 @ X25 @ 
% 0.22/0.48                 (k3_yellow19 @ X25 @ (k2_struct_0 @ X25) @ X24)))
% 0.22/0.48          | ~ (l1_struct_0 @ X25)
% 0.22/0.48          | (v2_struct_0 @ X25))),
% 0.22/0.48      inference('demod', [status(thm)], ['7', '8', '9', '10', '11'])).
% 0.22/0.48  thf('13', plain,
% 0.22/0.48      (((v2_struct_0 @ sk_A)
% 0.22/0.48        | ~ (l1_struct_0 @ sk_A)
% 0.22/0.48        | ((k7_subset_1 @ 
% 0.22/0.48            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.22/0.48            sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.22/0.48            = (k2_yellow19 @ sk_A @ 
% 0.22/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.22/0.48        | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.22/0.48             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.22/0.48        | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.22/0.48             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.22/0.48        | (v1_xboole_0 @ sk_B_1))),
% 0.22/0.48      inference('sup-', [status(thm)], ['6', '12'])).
% 0.22/0.48  thf('14', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('15', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_B_1 @ 
% 0.22/0.48        (k1_zfmisc_1 @ 
% 0.22/0.48         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.22/0.48      inference('demod', [status(thm)], ['4', '5'])).
% 0.22/0.48  thf(redefinition_k7_subset_1, axiom,
% 0.22/0.48    (![A:$i,B:$i,C:$i]:
% 0.22/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.48       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.22/0.48  thf('16', plain,
% 0.22/0.48      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 0.22/0.48          | ((k7_subset_1 @ X19 @ X18 @ X20) = (k4_xboole_0 @ X18 @ X20)))),
% 0.22/0.48      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.22/0.48  thf('17', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((k7_subset_1 @ 
% 0.22/0.48           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.22/0.48           sk_B_1 @ X0) = (k4_xboole_0 @ sk_B_1 @ X0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.48  thf('18', plain,
% 0.22/0.48      ((v13_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('19', plain,
% 0.22/0.48      (![X23 : $i]: ((k3_yellow_1 @ X23) = (k3_lattice3 @ (k1_lattice3 @ X23)))),
% 0.22/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.22/0.48  thf('20', plain,
% 0.22/0.48      ((v13_waybel_0 @ sk_B_1 @ 
% 0.22/0.48        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.22/0.48      inference('demod', [status(thm)], ['18', '19'])).
% 0.22/0.48  thf('21', plain,
% 0.22/0.48      ((v2_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('22', plain,
% 0.22/0.48      (![X23 : $i]: ((k3_yellow_1 @ X23) = (k3_lattice3 @ (k1_lattice3 @ X23)))),
% 0.22/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.22/0.48  thf('23', plain,
% 0.22/0.48      ((v2_waybel_0 @ sk_B_1 @ 
% 0.22/0.48        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.22/0.48      inference('demod', [status(thm)], ['21', '22'])).
% 0.22/0.48  thf('24', plain,
% 0.22/0.48      (((v2_struct_0 @ sk_A)
% 0.22/0.48        | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.22/0.48            = (k2_yellow19 @ sk_A @ 
% 0.22/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.22/0.48        | (v1_xboole_0 @ sk_B_1))),
% 0.22/0.48      inference('demod', [status(thm)], ['13', '14', '17', '20', '23'])).
% 0.22/0.48  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('26', plain,
% 0.22/0.48      (((v1_xboole_0 @ sk_B_1)
% 0.22/0.48        | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.22/0.48            = (k2_yellow19 @ sk_A @ 
% 0.22/0.48               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))),
% 0.22/0.48      inference('clc', [status(thm)], ['24', '25'])).
% 0.22/0.48  thf('27', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('28', plain,
% 0.22/0.48      (((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.22/0.48         = (k2_yellow19 @ sk_A @ 
% 0.22/0.48            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.22/0.48      inference('clc', [status(thm)], ['26', '27'])).
% 0.22/0.48  thf('29', plain,
% 0.22/0.48      (((sk_B_1) != (k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0)))),
% 0.22/0.48      inference('demod', [status(thm)], ['3', '28'])).
% 0.22/0.48  thf('30', plain,
% 0.22/0.48      ((((sk_B_1) != (sk_B_1)) | (r2_hidden @ k1_xboole_0 @ sk_B_1))),
% 0.22/0.48      inference('sup-', [status(thm)], ['2', '29'])).
% 0.22/0.48  thf('31', plain, ((r2_hidden @ k1_xboole_0 @ sk_B_1)),
% 0.22/0.48      inference('simplify', [status(thm)], ['30'])).
% 0.22/0.48  thf('32', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_B_1 @ 
% 0.22/0.48        (k1_zfmisc_1 @ 
% 0.22/0.48         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.22/0.48      inference('demod', [status(thm)], ['4', '5'])).
% 0.22/0.48  thf(t2_yellow19, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.22/0.48             ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 0.22/0.48             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.22/0.48             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.22/0.48             ( m1_subset_1 @
% 0.22/0.48               B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 0.22/0.48           ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ))).
% 0.22/0.48  thf('33', plain,
% 0.22/0.48      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.22/0.48         ((v1_xboole_0 @ X26)
% 0.22/0.48          | ~ (v1_subset_1 @ X26 @ (u1_struct_0 @ (k3_yellow_1 @ X27)))
% 0.22/0.48          | ~ (v2_waybel_0 @ X26 @ (k3_yellow_1 @ X27))
% 0.22/0.48          | ~ (v13_waybel_0 @ X26 @ (k3_yellow_1 @ X27))
% 0.22/0.48          | ~ (m1_subset_1 @ X26 @ 
% 0.22/0.48               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X27))))
% 0.22/0.48          | ~ (r2_hidden @ X28 @ X26)
% 0.22/0.48          | ~ (v1_xboole_0 @ X28)
% 0.22/0.48          | (v1_xboole_0 @ X27))),
% 0.22/0.48      inference('cnf', [status(esa)], [t2_yellow19])).
% 0.22/0.48  thf('34', plain,
% 0.22/0.48      (![X23 : $i]: ((k3_yellow_1 @ X23) = (k3_lattice3 @ (k1_lattice3 @ X23)))),
% 0.22/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.22/0.48  thf('35', plain,
% 0.22/0.48      (![X23 : $i]: ((k3_yellow_1 @ X23) = (k3_lattice3 @ (k1_lattice3 @ X23)))),
% 0.22/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.22/0.48  thf('36', plain,
% 0.22/0.48      (![X23 : $i]: ((k3_yellow_1 @ X23) = (k3_lattice3 @ (k1_lattice3 @ X23)))),
% 0.22/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.22/0.48  thf('37', plain,
% 0.22/0.48      (![X23 : $i]: ((k3_yellow_1 @ X23) = (k3_lattice3 @ (k1_lattice3 @ X23)))),
% 0.22/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.22/0.48  thf('38', plain,
% 0.22/0.48      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.22/0.48         ((v1_xboole_0 @ X26)
% 0.22/0.48          | ~ (v1_subset_1 @ X26 @ 
% 0.22/0.48               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X27))))
% 0.22/0.48          | ~ (v2_waybel_0 @ X26 @ (k3_lattice3 @ (k1_lattice3 @ X27)))
% 0.22/0.48          | ~ (v13_waybel_0 @ X26 @ (k3_lattice3 @ (k1_lattice3 @ X27)))
% 0.22/0.48          | ~ (m1_subset_1 @ X26 @ 
% 0.22/0.48               (k1_zfmisc_1 @ 
% 0.22/0.48                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X27)))))
% 0.22/0.48          | ~ (r2_hidden @ X28 @ X26)
% 0.22/0.48          | ~ (v1_xboole_0 @ X28)
% 0.22/0.48          | (v1_xboole_0 @ X27))),
% 0.22/0.48      inference('demod', [status(thm)], ['33', '34', '35', '36', '37'])).
% 0.22/0.48  thf('39', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.22/0.48          | ~ (v1_xboole_0 @ X0)
% 0.22/0.48          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.22/0.48          | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.22/0.48               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.22/0.48          | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.22/0.48               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.22/0.48          | ~ (v1_subset_1 @ sk_B_1 @ 
% 0.22/0.48               (u1_struct_0 @ 
% 0.22/0.48                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.22/0.48          | (v1_xboole_0 @ sk_B_1))),
% 0.22/0.48      inference('sup-', [status(thm)], ['32', '38'])).
% 0.22/0.48  thf('40', plain,
% 0.22/0.48      ((v13_waybel_0 @ sk_B_1 @ 
% 0.22/0.48        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.22/0.48      inference('demod', [status(thm)], ['18', '19'])).
% 0.22/0.48  thf('41', plain,
% 0.22/0.48      ((v2_waybel_0 @ sk_B_1 @ 
% 0.22/0.48        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.22/0.48      inference('demod', [status(thm)], ['21', '22'])).
% 0.22/0.48  thf('42', plain,
% 0.22/0.48      ((v1_subset_1 @ sk_B_1 @ 
% 0.22/0.48        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('43', plain,
% 0.22/0.48      (![X23 : $i]: ((k3_yellow_1 @ X23) = (k3_lattice3 @ (k1_lattice3 @ X23)))),
% 0.22/0.48      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.22/0.48  thf('44', plain,
% 0.22/0.48      ((v1_subset_1 @ sk_B_1 @ 
% 0.22/0.48        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.22/0.48      inference('demod', [status(thm)], ['42', '43'])).
% 0.22/0.48  thf('45', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.22/0.48          | ~ (v1_xboole_0 @ X0)
% 0.22/0.48          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.22/0.48          | (v1_xboole_0 @ sk_B_1))),
% 0.22/0.48      inference('demod', [status(thm)], ['39', '40', '41', '44'])).
% 0.22/0.49  thf('46', plain,
% 0.22/0.49      (((v1_xboole_0 @ sk_B_1)
% 0.22/0.49        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.22/0.49        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['31', '45'])).
% 0.22/0.49  thf(d1_xboole_0, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.49  thf('47', plain,
% 0.22/0.49      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.22/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.49  thf(t2_boole, axiom,
% 0.22/0.49    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.49  thf('48', plain,
% 0.22/0.49      (![X9 : $i]: ((k3_xboole_0 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.49  thf(t4_xboole_0, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.49            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.49       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.22/0.49            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.22/0.49  thf('49', plain,
% 0.22/0.49      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.22/0.49          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.22/0.49      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.22/0.49  thf('50', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['48', '49'])).
% 0.22/0.49  thf(t3_boole, axiom,
% 0.22/0.49    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.49  thf('51', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.22/0.49      inference('cnf', [status(esa)], [t3_boole])).
% 0.22/0.49  thf(t79_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.22/0.49  thf('52', plain,
% 0.22/0.49      (![X13 : $i, X14 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X14)),
% 0.22/0.49      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.22/0.49  thf('53', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.22/0.49      inference('sup+', [status(thm)], ['51', '52'])).
% 0.22/0.49  thf('54', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.22/0.49      inference('demod', [status(thm)], ['50', '53'])).
% 0.22/0.49  thf('55', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.49      inference('sup-', [status(thm)], ['47', '54'])).
% 0.22/0.49  thf('56', plain,
% 0.22/0.49      (((v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.22/0.49      inference('demod', [status(thm)], ['46', '55'])).
% 0.22/0.49  thf('57', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('58', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 0.22/0.49      inference('clc', [status(thm)], ['56', '57'])).
% 0.22/0.49  thf('59', plain,
% 0.22/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.49      inference('sup+', [status(thm)], ['1', '58'])).
% 0.22/0.49  thf('60', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('61', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['59', '60'])).
% 0.22/0.49  thf(fc2_struct_0, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.49       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.49  thf('62', plain,
% 0.22/0.49      (![X22 : $i]:
% 0.22/0.49         (~ (v1_xboole_0 @ (u1_struct_0 @ X22))
% 0.22/0.49          | ~ (l1_struct_0 @ X22)
% 0.22/0.49          | (v2_struct_0 @ X22))),
% 0.22/0.49      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.22/0.49  thf('63', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['61', '62'])).
% 0.22/0.49  thf('64', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('65', plain, ((v2_struct_0 @ sk_A)),
% 0.22/0.49      inference('demod', [status(thm)], ['63', '64'])).
% 0.22/0.49  thf('66', plain, ($false), inference('demod', [status(thm)], ['0', '65'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
