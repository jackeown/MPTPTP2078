%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zGlWBa9zfd

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 180 expanded)
%              Number of leaves         :   36 (  73 expanded)
%              Depth                    :   18
%              Number of atoms          :  935 (2480 expanded)
%              Number of equality atoms :   41 (  99 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

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
    ~ ( v1_xboole_0 @ sk_B ) ),
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
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X9 ) @ ( k1_tarski @ X10 ) )
      | ( X9 = X10 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X7 ) @ X8 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
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

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('7',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('9',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( v1_subset_1 @ X19 @ ( u1_struct_0 @ ( k3_yellow_1 @ X20 ) ) )
      | ~ ( v2_waybel_0 @ X19 @ ( k3_yellow_1 @ X20 ) )
      | ~ ( v13_waybel_0 @ X19 @ ( k3_yellow_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X20 ) ) ) )
      | ~ ( r2_hidden @ X21 @ X19 )
      | ~ ( v1_xboole_0 @ X21 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t2_yellow19])).

thf('15',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('16',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('17',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('18',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('19',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( v1_subset_1 @ X19 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) )
      | ~ ( v2_waybel_0 @ X19 @ ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) )
      | ~ ( v13_waybel_0 @ X19 @ ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X20 ) ) ) ) )
      | ~ ( r2_hidden @ X21 @ X19 )
      | ~ ( v1_xboole_0 @ X21 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('21',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('22',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('24',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('26',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('29',plain,(
    v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('31',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('36',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('38',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','27','34','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_xboole_0 @ ( sk_C @ X0 @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k1_tarski @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_xboole_0 @ sk_B @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_xboole_0 @ sk_B @ ( k1_tarski @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('46',plain,(
    ! [X15: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k1_tarski @ X0 ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k1_tarski @ X0 ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('50',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ X0 ) )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    sk_B
 != ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

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
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( v2_waybel_0 @ X17 @ ( k3_yellow_1 @ ( k2_struct_0 @ X18 ) ) )
      | ~ ( v13_waybel_0 @ X17 @ ( k3_yellow_1 @ ( k2_struct_0 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X18 ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X18 ) ) ) @ X17 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X18 @ ( k3_yellow19 @ X18 @ ( k2_struct_0 @ X18 ) @ X17 ) ) )
      | ~ ( l1_struct_0 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow19])).

thf('55',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('56',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('57',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('58',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('59',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( v2_waybel_0 @ X17 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X18 ) ) ) )
      | ~ ( v13_waybel_0 @ X17 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X18 ) ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X18 ) ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X18 ) ) ) ) @ X17 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X18 @ ( k3_yellow19 @ X18 @ ( k2_struct_0 @ X18 ) @ X17 ) ) )
      | ~ ( l1_struct_0 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(demod,[status(thm)],['54','55','56','57','58'])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['53','59'])).

thf('61',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('63',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( ( k7_subset_1 @ X12 @ X11 @ X13 )
        = ( k4_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('66',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['60','61','64','65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ k1_xboole_0 ) )
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    sk_B
 != ( k4_xboole_0 @ sk_B @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['52','71'])).

thf('73',plain,
    ( ( sk_B != sk_B )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','72'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('74',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('75',plain,
    ( ( sk_B != sk_B )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    $false ),
    inference(demod,[status(thm)],['0','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zGlWBa9zfd
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:41:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 156 iterations in 0.077s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.21/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.21/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.53  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.21/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.53  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.53  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.21/0.53  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.53  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.21/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.53  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.21/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.53  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.21/0.53  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.21/0.53  thf(t15_yellow19, conjecture,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.53             ( v1_subset_1 @
% 0.21/0.53               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.21/0.53             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.53             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.53             ( m1_subset_1 @
% 0.21/0.53               B @ 
% 0.21/0.53               ( k1_zfmisc_1 @
% 0.21/0.53                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.21/0.53           ( ( B ) =
% 0.21/0.53             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i]:
% 0.21/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.53          ( ![B:$i]:
% 0.21/0.53            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.53                ( v1_subset_1 @
% 0.21/0.53                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.21/0.53                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.53                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.53                ( m1_subset_1 @
% 0.21/0.53                  B @ 
% 0.21/0.53                  ( k1_zfmisc_1 @
% 0.21/0.53                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.21/0.53              ( ( B ) =
% 0.21/0.53                ( k2_yellow19 @
% 0.21/0.53                  A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t15_yellow19])).
% 0.21/0.53  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t3_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.21/0.53            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.53       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.53            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.53  thf(t17_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( A ) != ( B ) ) =>
% 0.21/0.53       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X9 : $i, X10 : $i]:
% 0.21/0.53         ((r1_xboole_0 @ (k1_tarski @ X9) @ (k1_tarski @ X10)) | ((X9) = (X10)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.21/0.53  thf(l24_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (![X7 : $i, X8 : $i]:
% 0.21/0.53         (~ (r1_xboole_0 @ (k1_tarski @ X7) @ X8) | ~ (r2_hidden @ X7 @ X8))),
% 0.21/0.53      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.21/0.53          | ((sk_C @ (k1_tarski @ X0) @ X1) = (X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['1', '4'])).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.21/0.53      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.53  thf(d3_struct_0, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (![X14 : $i]:
% 0.21/0.53         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_B @ 
% 0.21/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(d2_yellow_1, axiom,
% 0.21/0.53    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_B @ 
% 0.21/0.53        (k1_zfmisc_1 @ 
% 0.21/0.53         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.21/0.53      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (((m1_subset_1 @ sk_B @ 
% 0.21/0.53         (k1_zfmisc_1 @ 
% 0.21/0.53          (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))
% 0.21/0.53        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.53      inference('sup+', [status(thm)], ['7', '10'])).
% 0.21/0.53  thf('12', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_B @ 
% 0.21/0.53        (k1_zfmisc_1 @ 
% 0.21/0.53         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.21/0.53      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.53  thf(t2_yellow19, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.53             ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 0.21/0.53             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.21/0.53             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.21/0.53             ( m1_subset_1 @
% 0.21/0.53               B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 0.21/0.53           ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ))).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.53         ((v1_xboole_0 @ X19)
% 0.21/0.53          | ~ (v1_subset_1 @ X19 @ (u1_struct_0 @ (k3_yellow_1 @ X20)))
% 0.21/0.53          | ~ (v2_waybel_0 @ X19 @ (k3_yellow_1 @ X20))
% 0.21/0.53          | ~ (v13_waybel_0 @ X19 @ (k3_yellow_1 @ X20))
% 0.21/0.53          | ~ (m1_subset_1 @ X19 @ 
% 0.21/0.53               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X20))))
% 0.21/0.53          | ~ (r2_hidden @ X21 @ X19)
% 0.21/0.53          | ~ (v1_xboole_0 @ X21)
% 0.21/0.53          | (v1_xboole_0 @ X20))),
% 0.21/0.53      inference('cnf', [status(esa)], [t2_yellow19])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.53         ((v1_xboole_0 @ X19)
% 0.21/0.53          | ~ (v1_subset_1 @ X19 @ 
% 0.21/0.53               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X20))))
% 0.21/0.53          | ~ (v2_waybel_0 @ X19 @ (k3_lattice3 @ (k1_lattice3 @ X20)))
% 0.21/0.53          | ~ (v13_waybel_0 @ X19 @ (k3_lattice3 @ (k1_lattice3 @ X20)))
% 0.21/0.53          | ~ (m1_subset_1 @ X19 @ 
% 0.21/0.53               (k1_zfmisc_1 @ 
% 0.21/0.53                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X20)))))
% 0.21/0.53          | ~ (r2_hidden @ X21 @ X19)
% 0.21/0.53          | ~ (v1_xboole_0 @ X21)
% 0.21/0.53          | (v1_xboole_0 @ X20))),
% 0.21/0.53      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | ~ (v1_xboole_0 @ X0)
% 0.21/0.53          | ~ (r2_hidden @ X0 @ sk_B)
% 0.21/0.53          | ~ (v13_waybel_0 @ sk_B @ 
% 0.21/0.53               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.21/0.53          | ~ (v2_waybel_0 @ sk_B @ 
% 0.21/0.53               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.21/0.53          | ~ (v1_subset_1 @ sk_B @ 
% 0.21/0.53               (u1_struct_0 @ 
% 0.21/0.53                (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))
% 0.21/0.53          | (v1_xboole_0 @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['13', '19'])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      (![X14 : $i]:
% 0.21/0.53         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      ((v13_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.53  thf('24', plain,
% 0.21/0.53      ((v13_waybel_0 @ sk_B @ 
% 0.21/0.53        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.53      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      (((v13_waybel_0 @ sk_B @ 
% 0.21/0.53         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.21/0.53        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.53      inference('sup+', [status(thm)], ['21', '24'])).
% 0.21/0.53  thf('26', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      ((v13_waybel_0 @ sk_B @ 
% 0.21/0.53        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.53      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      (![X14 : $i]:
% 0.21/0.53         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      ((v2_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      ((v2_waybel_0 @ sk_B @ 
% 0.21/0.53        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.53      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.53  thf('32', plain,
% 0.21/0.53      (((v2_waybel_0 @ sk_B @ 
% 0.21/0.53         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.21/0.53        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.53      inference('sup+', [status(thm)], ['28', '31'])).
% 0.21/0.53  thf('33', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('34', plain,
% 0.21/0.53      ((v2_waybel_0 @ sk_B @ 
% 0.21/0.53        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.53      inference('demod', [status(thm)], ['32', '33'])).
% 0.21/0.53  thf('35', plain,
% 0.21/0.53      (![X14 : $i]:
% 0.21/0.53         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.53  thf('36', plain,
% 0.21/0.53      ((v1_subset_1 @ sk_B @ 
% 0.21/0.53        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('37', plain,
% 0.21/0.53      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.53  thf('38', plain,
% 0.21/0.53      ((v1_subset_1 @ sk_B @ 
% 0.21/0.53        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.21/0.53      inference('demod', [status(thm)], ['36', '37'])).
% 0.21/0.53  thf('39', plain,
% 0.21/0.53      (((v1_subset_1 @ sk_B @ 
% 0.21/0.53         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))
% 0.21/0.53        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.53      inference('sup+', [status(thm)], ['35', '38'])).
% 0.21/0.53  thf('40', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('41', plain,
% 0.21/0.53      ((v1_subset_1 @ sk_B @ 
% 0.21/0.53        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.53      inference('demod', [status(thm)], ['39', '40'])).
% 0.21/0.53  thf('42', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | ~ (v1_xboole_0 @ X0)
% 0.21/0.53          | ~ (r2_hidden @ X0 @ sk_B)
% 0.21/0.53          | (v1_xboole_0 @ sk_B))),
% 0.21/0.53      inference('demod', [status(thm)], ['20', '27', '34', '41'])).
% 0.21/0.53  thf('43', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r1_xboole_0 @ sk_B @ X0)
% 0.21/0.53          | (v1_xboole_0 @ sk_B)
% 0.21/0.53          | ~ (v1_xboole_0 @ (sk_C @ X0 @ sk_B))
% 0.21/0.53          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['6', '42'])).
% 0.21/0.53  thf('44', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v1_xboole_0 @ X0)
% 0.21/0.53          | (r1_xboole_0 @ sk_B @ (k1_tarski @ X0))
% 0.21/0.53          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | (v1_xboole_0 @ sk_B)
% 0.21/0.53          | (r1_xboole_0 @ sk_B @ (k1_tarski @ X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['5', '43'])).
% 0.21/0.53  thf('45', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v1_xboole_0 @ sk_B)
% 0.21/0.53          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.53          | (r1_xboole_0 @ sk_B @ (k1_tarski @ X0))
% 0.21/0.53          | ~ (v1_xboole_0 @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['44'])).
% 0.21/0.53  thf(fc2_struct_0, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.53       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.53  thf('46', plain,
% 0.21/0.53      (![X15 : $i]:
% 0.21/0.53         (~ (v1_xboole_0 @ (u1_struct_0 @ X15))
% 0.21/0.53          | ~ (l1_struct_0 @ X15)
% 0.21/0.53          | (v2_struct_0 @ X15))),
% 0.21/0.53      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.53  thf('47', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v1_xboole_0 @ X0)
% 0.21/0.53          | (r1_xboole_0 @ sk_B @ (k1_tarski @ X0))
% 0.21/0.53          | (v1_xboole_0 @ sk_B)
% 0.21/0.53          | (v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.53  thf('48', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('49', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v1_xboole_0 @ X0)
% 0.21/0.53          | (r1_xboole_0 @ sk_B @ (k1_tarski @ X0))
% 0.21/0.53          | (v1_xboole_0 @ sk_B)
% 0.21/0.53          | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['47', '48'])).
% 0.21/0.53  thf(t83_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.53  thf('50', plain,
% 0.21/0.53      (![X4 : $i, X5 : $i]:
% 0.21/0.53         (((k4_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.21/0.53      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.53  thf('51', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | (v1_xboole_0 @ sk_B)
% 0.21/0.53          | ~ (v1_xboole_0 @ X0)
% 0.21/0.53          | ((k4_xboole_0 @ sk_B @ (k1_tarski @ X0)) = (sk_B)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.53  thf('52', plain,
% 0.21/0.53      (((sk_B)
% 0.21/0.53         != (k2_yellow19 @ sk_A @ 
% 0.21/0.53             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('53', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_B @ 
% 0.21/0.53        (k1_zfmisc_1 @ 
% 0.21/0.53         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.21/0.53      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.53  thf(t14_yellow19, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.53             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.53             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.53             ( m1_subset_1 @
% 0.21/0.53               B @ 
% 0.21/0.53               ( k1_zfmisc_1 @
% 0.21/0.53                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.21/0.53           ( ( k7_subset_1 @
% 0.21/0.53               ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ 
% 0.21/0.53               ( k1_tarski @ k1_xboole_0 ) ) =
% 0.21/0.53             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.21/0.53  thf('54', plain,
% 0.21/0.53      (![X17 : $i, X18 : $i]:
% 0.21/0.53         ((v1_xboole_0 @ X17)
% 0.21/0.53          | ~ (v2_waybel_0 @ X17 @ (k3_yellow_1 @ (k2_struct_0 @ X18)))
% 0.21/0.53          | ~ (v13_waybel_0 @ X17 @ (k3_yellow_1 @ (k2_struct_0 @ X18)))
% 0.21/0.53          | ~ (m1_subset_1 @ X17 @ 
% 0.21/0.53               (k1_zfmisc_1 @ 
% 0.21/0.53                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X18)))))
% 0.21/0.53          | ((k7_subset_1 @ 
% 0.21/0.53              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X18))) @ X17 @ 
% 0.21/0.53              (k1_tarski @ k1_xboole_0))
% 0.21/0.53              = (k2_yellow19 @ X18 @ 
% 0.21/0.53                 (k3_yellow19 @ X18 @ (k2_struct_0 @ X18) @ X17)))
% 0.21/0.53          | ~ (l1_struct_0 @ X18)
% 0.21/0.53          | (v2_struct_0 @ X18))),
% 0.21/0.53      inference('cnf', [status(esa)], [t14_yellow19])).
% 0.21/0.53  thf('55', plain,
% 0.21/0.53      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.53  thf('56', plain,
% 0.21/0.53      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.53  thf('57', plain,
% 0.21/0.53      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.53  thf('58', plain,
% 0.21/0.53      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k3_lattice3 @ (k1_lattice3 @ X16)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.53  thf('59', plain,
% 0.21/0.53      (![X17 : $i, X18 : $i]:
% 0.21/0.53         ((v1_xboole_0 @ X17)
% 0.21/0.53          | ~ (v2_waybel_0 @ X17 @ 
% 0.21/0.53               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X18))))
% 0.21/0.53          | ~ (v13_waybel_0 @ X17 @ 
% 0.21/0.53               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X18))))
% 0.21/0.53          | ~ (m1_subset_1 @ X17 @ 
% 0.21/0.53               (k1_zfmisc_1 @ 
% 0.21/0.53                (u1_struct_0 @ 
% 0.21/0.53                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X18))))))
% 0.21/0.53          | ((k7_subset_1 @ 
% 0.21/0.53              (u1_struct_0 @ 
% 0.21/0.53               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X18)))) @ 
% 0.21/0.53              X17 @ (k1_tarski @ k1_xboole_0))
% 0.21/0.53              = (k2_yellow19 @ X18 @ 
% 0.21/0.53                 (k3_yellow19 @ X18 @ (k2_struct_0 @ X18) @ X17)))
% 0.21/0.53          | ~ (l1_struct_0 @ X18)
% 0.21/0.53          | (v2_struct_0 @ X18))),
% 0.21/0.53      inference('demod', [status(thm)], ['54', '55', '56', '57', '58'])).
% 0.21/0.53  thf('60', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_A)
% 0.21/0.53        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.53        | ((k7_subset_1 @ 
% 0.21/0.53            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.21/0.53            sk_B @ (k1_tarski @ k1_xboole_0))
% 0.21/0.53            = (k2_yellow19 @ sk_A @ 
% 0.21/0.53               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.21/0.53        | ~ (v13_waybel_0 @ sk_B @ 
% 0.21/0.53             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.21/0.53        | ~ (v2_waybel_0 @ sk_B @ 
% 0.21/0.53             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.21/0.53        | (v1_xboole_0 @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['53', '59'])).
% 0.21/0.53  thf('61', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('62', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_B @ 
% 0.21/0.53        (k1_zfmisc_1 @ 
% 0.21/0.53         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.21/0.53      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.53  thf(redefinition_k7_subset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.53       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.21/0.53  thf('63', plain,
% 0.21/0.53      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.21/0.53          | ((k7_subset_1 @ X12 @ X11 @ X13) = (k4_xboole_0 @ X11 @ X13)))),
% 0.21/0.53      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.21/0.53  thf('64', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((k7_subset_1 @ 
% 0.21/0.53           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 0.21/0.53           sk_B @ X0) = (k4_xboole_0 @ sk_B @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['62', '63'])).
% 0.21/0.53  thf('65', plain,
% 0.21/0.53      ((v13_waybel_0 @ sk_B @ 
% 0.21/0.53        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.53      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.53  thf('66', plain,
% 0.21/0.53      ((v2_waybel_0 @ sk_B @ 
% 0.21/0.53        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.53      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.53  thf('67', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_A)
% 0.21/0.53        | ((k4_xboole_0 @ sk_B @ (k1_tarski @ k1_xboole_0))
% 0.21/0.53            = (k2_yellow19 @ sk_A @ 
% 0.21/0.53               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.21/0.53        | (v1_xboole_0 @ sk_B))),
% 0.21/0.53      inference('demod', [status(thm)], ['60', '61', '64', '65', '66'])).
% 0.21/0.53  thf('68', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('69', plain,
% 0.21/0.53      (((v1_xboole_0 @ sk_B)
% 0.21/0.53        | ((k4_xboole_0 @ sk_B @ (k1_tarski @ k1_xboole_0))
% 0.21/0.53            = (k2_yellow19 @ sk_A @ 
% 0.21/0.53               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.21/0.53      inference('clc', [status(thm)], ['67', '68'])).
% 0.21/0.53  thf('70', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('71', plain,
% 0.21/0.53      (((k4_xboole_0 @ sk_B @ (k1_tarski @ k1_xboole_0))
% 0.21/0.53         = (k2_yellow19 @ sk_A @ 
% 0.21/0.53            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.21/0.53      inference('clc', [status(thm)], ['69', '70'])).
% 0.21/0.53  thf('72', plain,
% 0.21/0.53      (((sk_B) != (k4_xboole_0 @ sk_B @ (k1_tarski @ k1_xboole_0)))),
% 0.21/0.53      inference('demod', [status(thm)], ['52', '71'])).
% 0.21/0.53  thf('73', plain,
% 0.21/0.53      ((((sk_B) != (sk_B))
% 0.21/0.53        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.53        | (v1_xboole_0 @ sk_B)
% 0.21/0.53        | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['51', '72'])).
% 0.21/0.53  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.53  thf('74', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.53  thf('75', plain,
% 0.21/0.53      ((((sk_B) != (sk_B)) | (v1_xboole_0 @ sk_B) | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['73', '74'])).
% 0.21/0.53  thf('76', plain, (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ sk_B))),
% 0.21/0.53      inference('simplify', [status(thm)], ['75'])).
% 0.21/0.53  thf('77', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('78', plain, ((v1_xboole_0 @ sk_B)),
% 0.21/0.53      inference('clc', [status(thm)], ['76', '77'])).
% 0.21/0.53  thf('79', plain, ($false), inference('demod', [status(thm)], ['0', '78'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
