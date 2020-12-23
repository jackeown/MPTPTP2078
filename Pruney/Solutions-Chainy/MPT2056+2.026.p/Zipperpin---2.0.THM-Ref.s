%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Kthy0GQzW5

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:43 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 175 expanded)
%              Number of leaves         :   36 (  72 expanded)
%              Depth                    :   22
%              Number of atoms          :  972 (2282 expanded)
%              Number of equality atoms :   49 ( 103 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X15: $i] :
      ( ( k2_tarski @ X15 @ X15 )
      = ( k1_tarski @ X15 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('1',plain,(
    ! [X15: $i] :
      ( ( k2_tarski @ X15 @ X15 )
      = ( k1_tarski @ X15 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

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
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X12 )
      | ( X13 = X10 )
      | ( X12
       != ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('4',plain,(
    ! [X10: $i,X13: $i] :
      ( ( X13 = X10 )
      | ~ ( r2_hidden @ X13 @ ( k1_tarski @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('8',plain,(
    ! [X10: $i,X13: $i] :
      ( ( X13 = X10 )
      | ~ ( r2_hidden @ X13 @ ( k1_tarski @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

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

thf('11',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('12',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('13',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

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

thf('14',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( v1_subset_1 @ X23 @ ( u1_struct_0 @ ( k3_yellow_1 @ X24 ) ) )
      | ~ ( v2_waybel_0 @ X23 @ ( k3_yellow_1 @ X24 ) )
      | ~ ( v13_waybel_0 @ X23 @ ( k3_yellow_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X24 ) ) ) )
      | ~ ( r2_hidden @ X25 @ X23 )
      | ~ ( v1_xboole_0 @ X25 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t2_yellow19])).

thf('15',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('16',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('17',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('18',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('19',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( v1_subset_1 @ X23 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X24 ) ) ) )
      | ~ ( v2_waybel_0 @ X23 @ ( k3_lattice3 @ ( k1_lattice3 @ X24 ) ) )
      | ~ ( v13_waybel_0 @ X23 @ ( k3_lattice3 @ ( k1_lattice3 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X24 ) ) ) ) )
      | ~ ( r2_hidden @ X25 @ X23 )
      | ~ ( v1_xboole_0 @ X25 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('21',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('23',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('26',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('29',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['20','23','26','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ ( sk_C @ sk_B_1 @ X0 ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['9','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('34',plain,(
    ! [X19: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( X11 != X10 )
      | ( r2_hidden @ X11 @ X12 )
      | ( X12
       != ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('39',plain,(
    ! [X10: $i] :
      ( r2_hidden @ X10 @ ( k1_tarski @ X10 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['37','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( sk_C @ X0 @ sk_B_1 ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ sk_B_1 @ ( k1_tarski @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( r1_xboole_0 @ sk_B_1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_xboole_0 @ sk_B_1 @ ( k1_tarski @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('46',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ X0 ) )
        = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B_1 @ ( k2_tarski @ X0 @ X0 ) )
        = sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','47'])).

thf('49',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( ( k4_xboole_0 @ sk_B_1 @ ( k2_tarski @ X0 @ X0 ) )
        = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B_1 @ ( k2_tarski @ X0 @ X0 ) )
        = sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ X0 ) )
        = sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','52'])).

thf('54',plain,(
    sk_B_1
 != ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

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

thf('56',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v1_xboole_0 @ X21 )
      | ~ ( v2_waybel_0 @ X21 @ ( k3_yellow_1 @ ( k2_struct_0 @ X22 ) ) )
      | ~ ( v13_waybel_0 @ X21 @ ( k3_yellow_1 @ ( k2_struct_0 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X22 ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X22 ) ) ) @ X21 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X22 @ ( k3_yellow19 @ X22 @ ( k2_struct_0 @ X22 ) @ X21 ) ) )
      | ~ ( l1_struct_0 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow19])).

thf('57',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('58',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('59',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('60',plain,(
    ! [X20: $i] :
      ( ( k3_yellow_1 @ X20 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('61',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v1_xboole_0 @ X21 )
      | ~ ( v2_waybel_0 @ X21 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X22 ) ) ) )
      | ~ ( v13_waybel_0 @ X21 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X22 ) ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X22 ) ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X22 ) ) ) ) @ X21 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X22 @ ( k3_yellow19 @ X22 @ ( k2_struct_0 @ X22 ) @ X21 ) ) )
      | ~ ( l1_struct_0 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(demod,[status(thm)],['56','57','58','59','60'])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['55','61'])).

thf('63',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('65',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( ( k7_subset_1 @ X17 @ X16 @ X18 )
        = ( k4_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_1 @ X0 )
      = ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('68',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['62','63','66','67','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,(
    sk_B_1
 != ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['54','73'])).

thf('75',plain,
    ( ( sk_B_1 != sk_B_1 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','74'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('76',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('77',plain,(
    sk_B_1 != sk_B_1 ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    $false ),
    inference(simplify,[status(thm)],['77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Kthy0GQzW5
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:24:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.36  % Running in FO mode
% 0.41/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.59  % Solved by: fo/fo7.sh
% 0.41/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.59  % done 285 iterations in 0.121s
% 0.41/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.59  % SZS output start Refutation
% 0.41/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.41/0.59  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.41/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.59  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.41/0.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.41/0.59  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.41/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.41/0.59  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.41/0.59  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.41/0.59  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.41/0.60  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.41/0.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.41/0.60  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.41/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.60  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.41/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.41/0.60  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.41/0.60  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.41/0.60  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.41/0.60  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.41/0.60  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.41/0.60  thf(t69_enumset1, axiom,
% 0.41/0.60    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.41/0.60  thf('0', plain, (![X15 : $i]: ((k2_tarski @ X15 @ X15) = (k1_tarski @ X15))),
% 0.41/0.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.41/0.60  thf('1', plain, (![X15 : $i]: ((k2_tarski @ X15 @ X15) = (k1_tarski @ X15))),
% 0.41/0.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.41/0.60  thf(t3_xboole_0, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.41/0.60            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.41/0.60       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.41/0.60            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.41/0.60  thf('2', plain,
% 0.41/0.60      (![X3 : $i, X4 : $i]:
% 0.41/0.60         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 0.41/0.60      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.41/0.60  thf(d1_tarski, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.41/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.41/0.60  thf('3', plain,
% 0.41/0.60      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X13 @ X12)
% 0.41/0.60          | ((X13) = (X10))
% 0.41/0.60          | ((X12) != (k1_tarski @ X10)))),
% 0.41/0.60      inference('cnf', [status(esa)], [d1_tarski])).
% 0.41/0.60  thf('4', plain,
% 0.41/0.60      (![X10 : $i, X13 : $i]:
% 0.41/0.60         (((X13) = (X10)) | ~ (r2_hidden @ X13 @ (k1_tarski @ X10)))),
% 0.41/0.60      inference('simplify', [status(thm)], ['3'])).
% 0.41/0.60  thf('5', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.41/0.60          | ((sk_C @ (k1_tarski @ X0) @ X1) = (X0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['2', '4'])).
% 0.41/0.60  thf('6', plain,
% 0.41/0.60      (![X3 : $i, X4 : $i]:
% 0.41/0.60         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.41/0.60      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.41/0.60  thf('7', plain,
% 0.41/0.60      (![X3 : $i, X4 : $i]:
% 0.41/0.60         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.41/0.60      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.41/0.60  thf('8', plain,
% 0.41/0.60      (![X10 : $i, X13 : $i]:
% 0.41/0.60         (((X13) = (X10)) | ~ (r2_hidden @ X13 @ (k1_tarski @ X10)))),
% 0.41/0.60      inference('simplify', [status(thm)], ['3'])).
% 0.41/0.60  thf('9', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.41/0.60          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['7', '8'])).
% 0.41/0.60  thf('10', plain,
% 0.41/0.60      (![X3 : $i, X4 : $i]:
% 0.41/0.60         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 0.41/0.60      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.41/0.60  thf(t15_yellow19, conjecture,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.41/0.60             ( v1_subset_1 @
% 0.41/0.60               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.41/0.60             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.41/0.60             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.41/0.60             ( m1_subset_1 @
% 0.41/0.60               B @ 
% 0.41/0.60               ( k1_zfmisc_1 @
% 0.41/0.60                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.41/0.60           ( ( B ) =
% 0.41/0.60             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.41/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.60    (~( ![A:$i]:
% 0.41/0.60        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.41/0.60          ( ![B:$i]:
% 0.41/0.60            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.41/0.60                ( v1_subset_1 @
% 0.41/0.60                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.41/0.60                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.41/0.60                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.41/0.60                ( m1_subset_1 @
% 0.41/0.60                  B @ 
% 0.41/0.60                  ( k1_zfmisc_1 @
% 0.41/0.60                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.41/0.60              ( ( B ) =
% 0.41/0.60                ( k2_yellow19 @
% 0.41/0.60                  A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.41/0.60    inference('cnf.neg', [status(esa)], [t15_yellow19])).
% 0.41/0.60  thf('11', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_B_1 @ 
% 0.41/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(d2_yellow_1, axiom,
% 0.41/0.60    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.41/0.60  thf('12', plain,
% 0.41/0.60      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.41/0.60      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.41/0.60  thf('13', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_B_1 @ 
% 0.41/0.60        (k1_zfmisc_1 @ 
% 0.41/0.60         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.41/0.60      inference('demod', [status(thm)], ['11', '12'])).
% 0.41/0.60  thf(t2_yellow19, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.41/0.60             ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 0.41/0.60             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.41/0.60             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.41/0.60             ( m1_subset_1 @
% 0.41/0.60               B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 0.41/0.60           ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ))).
% 0.41/0.60  thf('14', plain,
% 0.41/0.60      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.41/0.60         ((v1_xboole_0 @ X23)
% 0.41/0.60          | ~ (v1_subset_1 @ X23 @ (u1_struct_0 @ (k3_yellow_1 @ X24)))
% 0.41/0.60          | ~ (v2_waybel_0 @ X23 @ (k3_yellow_1 @ X24))
% 0.41/0.60          | ~ (v13_waybel_0 @ X23 @ (k3_yellow_1 @ X24))
% 0.41/0.60          | ~ (m1_subset_1 @ X23 @ 
% 0.41/0.60               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X24))))
% 0.41/0.60          | ~ (r2_hidden @ X25 @ X23)
% 0.41/0.60          | ~ (v1_xboole_0 @ X25)
% 0.41/0.60          | (v1_xboole_0 @ X24))),
% 0.41/0.60      inference('cnf', [status(esa)], [t2_yellow19])).
% 0.41/0.60  thf('15', plain,
% 0.41/0.60      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.41/0.60      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.41/0.60  thf('16', plain,
% 0.41/0.60      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.41/0.60      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.41/0.60  thf('17', plain,
% 0.41/0.60      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.41/0.60      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.41/0.60  thf('18', plain,
% 0.41/0.60      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.41/0.60      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.41/0.60  thf('19', plain,
% 0.41/0.60      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.41/0.60         ((v1_xboole_0 @ X23)
% 0.41/0.60          | ~ (v1_subset_1 @ X23 @ 
% 0.41/0.60               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X24))))
% 0.41/0.60          | ~ (v2_waybel_0 @ X23 @ (k3_lattice3 @ (k1_lattice3 @ X24)))
% 0.41/0.60          | ~ (v13_waybel_0 @ X23 @ (k3_lattice3 @ (k1_lattice3 @ X24)))
% 0.41/0.60          | ~ (m1_subset_1 @ X23 @ 
% 0.41/0.60               (k1_zfmisc_1 @ 
% 0.41/0.60                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X24)))))
% 0.41/0.60          | ~ (r2_hidden @ X25 @ X23)
% 0.41/0.60          | ~ (v1_xboole_0 @ X25)
% 0.41/0.60          | (v1_xboole_0 @ X24))),
% 0.41/0.60      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.41/0.60  thf('20', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.41/0.60          | ~ (v1_xboole_0 @ X0)
% 0.41/0.60          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.41/0.60          | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.41/0.60               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.41/0.60          | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.41/0.60               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.41/0.60          | ~ (v1_subset_1 @ sk_B_1 @ 
% 0.41/0.60               (u1_struct_0 @ 
% 0.41/0.60                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.41/0.60          | (v1_xboole_0 @ sk_B_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['13', '19'])).
% 0.41/0.60  thf('21', plain,
% 0.41/0.60      ((v13_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('22', plain,
% 0.41/0.60      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.41/0.60      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.41/0.60  thf('23', plain,
% 0.41/0.60      ((v13_waybel_0 @ sk_B_1 @ 
% 0.41/0.60        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.41/0.60      inference('demod', [status(thm)], ['21', '22'])).
% 0.41/0.60  thf('24', plain,
% 0.41/0.60      ((v2_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('25', plain,
% 0.41/0.60      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.41/0.60      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.41/0.60  thf('26', plain,
% 0.41/0.60      ((v2_waybel_0 @ sk_B_1 @ 
% 0.41/0.60        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.41/0.60      inference('demod', [status(thm)], ['24', '25'])).
% 0.41/0.60  thf('27', plain,
% 0.41/0.60      ((v1_subset_1 @ sk_B_1 @ 
% 0.41/0.60        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('28', plain,
% 0.41/0.60      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.41/0.60      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.41/0.60  thf('29', plain,
% 0.41/0.60      ((v1_subset_1 @ sk_B_1 @ 
% 0.41/0.60        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.41/0.60      inference('demod', [status(thm)], ['27', '28'])).
% 0.41/0.60  thf('30', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.41/0.60          | ~ (v1_xboole_0 @ X0)
% 0.41/0.60          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.41/0.60          | (v1_xboole_0 @ sk_B_1))),
% 0.41/0.60      inference('demod', [status(thm)], ['20', '23', '26', '29'])).
% 0.41/0.60  thf('31', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((r1_xboole_0 @ X0 @ sk_B_1)
% 0.41/0.60          | (v1_xboole_0 @ sk_B_1)
% 0.41/0.60          | ~ (v1_xboole_0 @ (sk_C @ sk_B_1 @ X0))
% 0.41/0.60          | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['10', '30'])).
% 0.41/0.60  thf('32', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (v1_xboole_0 @ X0)
% 0.41/0.60          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_1)
% 0.41/0.60          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.41/0.60          | (v1_xboole_0 @ sk_B_1)
% 0.41/0.60          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['9', '31'])).
% 0.41/0.60  thf('33', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((v1_xboole_0 @ sk_B_1)
% 0.41/0.60          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.41/0.60          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_1)
% 0.41/0.60          | ~ (v1_xboole_0 @ X0))),
% 0.41/0.60      inference('simplify', [status(thm)], ['32'])).
% 0.41/0.60  thf(fc5_struct_0, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.41/0.60       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.41/0.60  thf('34', plain,
% 0.41/0.60      (![X19 : $i]:
% 0.41/0.60         (~ (v1_xboole_0 @ (k2_struct_0 @ X19))
% 0.41/0.60          | ~ (l1_struct_0 @ X19)
% 0.41/0.60          | (v2_struct_0 @ X19))),
% 0.41/0.60      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.41/0.60  thf('35', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (v1_xboole_0 @ X0)
% 0.41/0.60          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_1)
% 0.41/0.60          | (v1_xboole_0 @ sk_B_1)
% 0.41/0.60          | (v2_struct_0 @ sk_A)
% 0.41/0.60          | ~ (l1_struct_0 @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['33', '34'])).
% 0.41/0.60  thf('36', plain, ((l1_struct_0 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('37', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (v1_xboole_0 @ X0)
% 0.41/0.60          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_1)
% 0.41/0.60          | (v1_xboole_0 @ sk_B_1)
% 0.41/0.60          | (v2_struct_0 @ sk_A))),
% 0.41/0.60      inference('demod', [status(thm)], ['35', '36'])).
% 0.41/0.60  thf('38', plain,
% 0.41/0.60      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.41/0.60         (((X11) != (X10))
% 0.41/0.60          | (r2_hidden @ X11 @ X12)
% 0.41/0.60          | ((X12) != (k1_tarski @ X10)))),
% 0.41/0.60      inference('cnf', [status(esa)], [d1_tarski])).
% 0.41/0.60  thf('39', plain, (![X10 : $i]: (r2_hidden @ X10 @ (k1_tarski @ X10))),
% 0.41/0.60      inference('simplify', [status(thm)], ['38'])).
% 0.41/0.60  thf('40', plain,
% 0.41/0.60      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X5 @ X3)
% 0.41/0.60          | ~ (r2_hidden @ X5 @ X6)
% 0.41/0.60          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.41/0.60      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.41/0.60  thf('41', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['39', '40'])).
% 0.41/0.60  thf('42', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((v2_struct_0 @ sk_A)
% 0.41/0.60          | (v1_xboole_0 @ sk_B_1)
% 0.41/0.60          | ~ (v1_xboole_0 @ X0)
% 0.41/0.60          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['37', '41'])).
% 0.41/0.60  thf('43', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((r1_xboole_0 @ sk_B_1 @ X0)
% 0.41/0.60          | ~ (v1_xboole_0 @ (sk_C @ X0 @ sk_B_1))
% 0.41/0.60          | (v1_xboole_0 @ sk_B_1)
% 0.41/0.60          | (v2_struct_0 @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['6', '42'])).
% 0.41/0.60  thf('44', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (v1_xboole_0 @ X0)
% 0.41/0.60          | (r1_xboole_0 @ sk_B_1 @ (k1_tarski @ X0))
% 0.41/0.60          | (v2_struct_0 @ sk_A)
% 0.41/0.60          | (v1_xboole_0 @ sk_B_1)
% 0.41/0.60          | (r1_xboole_0 @ sk_B_1 @ (k1_tarski @ X0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['5', '43'])).
% 0.41/0.60  thf('45', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((v1_xboole_0 @ sk_B_1)
% 0.41/0.60          | (v2_struct_0 @ sk_A)
% 0.41/0.60          | (r1_xboole_0 @ sk_B_1 @ (k1_tarski @ X0))
% 0.41/0.60          | ~ (v1_xboole_0 @ X0))),
% 0.41/0.60      inference('simplify', [status(thm)], ['44'])).
% 0.41/0.60  thf(t83_xboole_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.41/0.60  thf('46', plain,
% 0.41/0.60      (![X7 : $i, X8 : $i]:
% 0.41/0.60         (((k4_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_xboole_0 @ X7 @ X8))),
% 0.41/0.60      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.41/0.60  thf('47', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (v1_xboole_0 @ X0)
% 0.41/0.60          | (v2_struct_0 @ sk_A)
% 0.41/0.60          | (v1_xboole_0 @ sk_B_1)
% 0.41/0.60          | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ X0)) = (sk_B_1)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['45', '46'])).
% 0.41/0.60  thf('48', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (((k4_xboole_0 @ sk_B_1 @ (k2_tarski @ X0 @ X0)) = (sk_B_1))
% 0.41/0.60          | (v1_xboole_0 @ sk_B_1)
% 0.41/0.60          | (v2_struct_0 @ sk_A)
% 0.41/0.60          | ~ (v1_xboole_0 @ X0))),
% 0.41/0.60      inference('sup+', [status(thm)], ['1', '47'])).
% 0.41/0.60  thf('49', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('50', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (v1_xboole_0 @ X0)
% 0.41/0.60          | (v2_struct_0 @ sk_A)
% 0.41/0.60          | ((k4_xboole_0 @ sk_B_1 @ (k2_tarski @ X0 @ X0)) = (sk_B_1)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['48', '49'])).
% 0.41/0.60  thf('51', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('52', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (((k4_xboole_0 @ sk_B_1 @ (k2_tarski @ X0 @ X0)) = (sk_B_1))
% 0.41/0.60          | ~ (v1_xboole_0 @ X0))),
% 0.41/0.60      inference('clc', [status(thm)], ['50', '51'])).
% 0.41/0.60  thf('53', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ X0)) = (sk_B_1))
% 0.41/0.60          | ~ (v1_xboole_0 @ X0))),
% 0.41/0.60      inference('sup+', [status(thm)], ['0', '52'])).
% 0.41/0.60  thf('54', plain,
% 0.41/0.60      (((sk_B_1)
% 0.41/0.60         != (k2_yellow19 @ sk_A @ 
% 0.41/0.60             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('55', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_B_1 @ 
% 0.41/0.60        (k1_zfmisc_1 @ 
% 0.41/0.60         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.41/0.60      inference('demod', [status(thm)], ['11', '12'])).
% 0.41/0.60  thf(t14_yellow19, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.41/0.60             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.41/0.60             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.41/0.60             ( m1_subset_1 @
% 0.41/0.60               B @ 
% 0.41/0.60               ( k1_zfmisc_1 @
% 0.41/0.60                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.41/0.60           ( ( k7_subset_1 @
% 0.41/0.60               ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ 
% 0.41/0.60               ( k1_tarski @ k1_xboole_0 ) ) =
% 0.41/0.60             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.41/0.60  thf('56', plain,
% 0.41/0.60      (![X21 : $i, X22 : $i]:
% 0.41/0.60         ((v1_xboole_0 @ X21)
% 0.41/0.60          | ~ (v2_waybel_0 @ X21 @ (k3_yellow_1 @ (k2_struct_0 @ X22)))
% 0.41/0.60          | ~ (v13_waybel_0 @ X21 @ (k3_yellow_1 @ (k2_struct_0 @ X22)))
% 0.41/0.60          | ~ (m1_subset_1 @ X21 @ 
% 0.41/0.60               (k1_zfmisc_1 @ 
% 0.41/0.60                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X22)))))
% 0.41/0.60          | ((k7_subset_1 @ 
% 0.41/0.60              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X22))) @ X21 @ 
% 0.41/0.60              (k1_tarski @ k1_xboole_0))
% 0.41/0.60              = (k2_yellow19 @ X22 @ 
% 0.41/0.60                 (k3_yellow19 @ X22 @ (k2_struct_0 @ X22) @ X21)))
% 0.41/0.60          | ~ (l1_struct_0 @ X22)
% 0.41/0.60          | (v2_struct_0 @ X22))),
% 0.41/0.60      inference('cnf', [status(esa)], [t14_yellow19])).
% 0.41/0.60  thf('57', plain,
% 0.41/0.60      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.41/0.60      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.41/0.60  thf('58', plain,
% 0.41/0.60      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.41/0.60      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.41/0.60  thf('59', plain,
% 0.41/0.60      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.41/0.60      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.41/0.60  thf('60', plain,
% 0.41/0.60      (![X20 : $i]: ((k3_yellow_1 @ X20) = (k3_lattice3 @ (k1_lattice3 @ X20)))),
% 0.41/0.60      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.41/0.60  thf('61', plain,
% 0.41/0.60      (![X21 : $i, X22 : $i]:
% 0.41/0.60         ((v1_xboole_0 @ X21)
% 0.41/0.60          | ~ (v2_waybel_0 @ X21 @ 
% 0.41/0.60               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X22))))
% 0.41/0.60          | ~ (v13_waybel_0 @ X21 @ 
% 0.41/0.60               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X22))))
% 0.41/0.60          | ~ (m1_subset_1 @ X21 @ 
% 0.41/0.60               (k1_zfmisc_1 @ 
% 0.41/0.60                (u1_struct_0 @ 
% 0.41/0.60                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X22))))))
% 0.41/0.60          | ((k7_subset_1 @ 
% 0.41/0.60              (u1_struct_0 @ 
% 0.41/0.60               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X22)))) @ 
% 0.41/0.60              X21 @ (k1_tarski @ k1_xboole_0))
% 0.41/0.60              = (k2_yellow19 @ X22 @ 
% 0.41/0.60                 (k3_yellow19 @ X22 @ (k2_struct_0 @ X22) @ X21)))
% 0.41/0.60          | ~ (l1_struct_0 @ X22)
% 0.41/0.60          | (v2_struct_0 @ X22))),
% 0.41/0.60      inference('demod', [status(thm)], ['56', '57', '58', '59', '60'])).
% 0.41/0.60  thf('62', plain,
% 0.41/0.60      (((v2_struct_0 @ sk_A)
% 0.41/0.60        | ~ (l1_struct_0 @ sk_A)
% 0.41/0.60        | ((k7_subset_1 @ 
% 0.41/0.60            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.41/0.60            sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.41/0.60            = (k2_yellow19 @ sk_A @ 
% 0.41/0.60               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.41/0.60        | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.41/0.60             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.41/0.60        | ~ (v2_waybel_0 @ sk_B_1 @ 
% 0.41/0.60             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.41/0.60        | (v1_xboole_0 @ sk_B_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['55', '61'])).
% 0.41/0.60  thf('63', plain, ((l1_struct_0 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('64', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_B_1 @ 
% 0.41/0.60        (k1_zfmisc_1 @ 
% 0.41/0.60         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.41/0.60      inference('demod', [status(thm)], ['11', '12'])).
% 0.41/0.60  thf(redefinition_k7_subset_1, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.60       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.41/0.60  thf('65', plain,
% 0.41/0.60      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.41/0.60          | ((k7_subset_1 @ X17 @ X16 @ X18) = (k4_xboole_0 @ X16 @ X18)))),
% 0.41/0.60      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.41/0.60  thf('66', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((k7_subset_1 @ 
% 0.41/0.60           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.41/0.60           sk_B_1 @ X0) = (k4_xboole_0 @ sk_B_1 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['64', '65'])).
% 0.41/0.60  thf('67', plain,
% 0.41/0.60      ((v13_waybel_0 @ sk_B_1 @ 
% 0.41/0.60        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.41/0.60      inference('demod', [status(thm)], ['21', '22'])).
% 0.41/0.60  thf('68', plain,
% 0.41/0.60      ((v2_waybel_0 @ sk_B_1 @ 
% 0.41/0.60        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.41/0.60      inference('demod', [status(thm)], ['24', '25'])).
% 0.41/0.60  thf('69', plain,
% 0.41/0.60      (((v2_struct_0 @ sk_A)
% 0.41/0.60        | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.41/0.60            = (k2_yellow19 @ sk_A @ 
% 0.41/0.60               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.41/0.60        | (v1_xboole_0 @ sk_B_1))),
% 0.41/0.60      inference('demod', [status(thm)], ['62', '63', '66', '67', '68'])).
% 0.41/0.60  thf('70', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('71', plain,
% 0.41/0.60      (((v1_xboole_0 @ sk_B_1)
% 0.41/0.60        | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.41/0.60            = (k2_yellow19 @ sk_A @ 
% 0.41/0.60               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))),
% 0.41/0.60      inference('clc', [status(thm)], ['69', '70'])).
% 0.41/0.60  thf('72', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('73', plain,
% 0.41/0.60      (((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.41/0.60         = (k2_yellow19 @ sk_A @ 
% 0.41/0.60            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.41/0.60      inference('clc', [status(thm)], ['71', '72'])).
% 0.41/0.60  thf('74', plain,
% 0.41/0.60      (((sk_B_1) != (k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0)))),
% 0.41/0.60      inference('demod', [status(thm)], ['54', '73'])).
% 0.41/0.60  thf('75', plain, ((((sk_B_1) != (sk_B_1)) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['53', '74'])).
% 0.41/0.60  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.41/0.60  thf('76', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.41/0.60      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.41/0.60  thf('77', plain, (((sk_B_1) != (sk_B_1))),
% 0.41/0.60      inference('demod', [status(thm)], ['75', '76'])).
% 0.41/0.60  thf('78', plain, ($false), inference('simplify', [status(thm)], ['77'])).
% 0.41/0.60  
% 0.41/0.60  % SZS output end Refutation
% 0.41/0.60  
% 0.41/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
