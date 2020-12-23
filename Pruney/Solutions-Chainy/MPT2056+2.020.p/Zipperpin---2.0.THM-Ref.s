%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hPrJVvPzIa

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:42 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 243 expanded)
%              Number of leaves         :   47 (  97 expanded)
%              Depth                    :   19
%              Number of atoms          : 1165 (2877 expanded)
%              Number of equality atoms :   55 ( 117 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C_1 @ X8 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X24 ) @ ( k1_tarski @ X25 ) )
      | ( X24 = X25 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('3',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X22 ) @ X23 )
      | ~ ( r2_hidden @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C_1 @ X8 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('7',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('8',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('9',plain,(
    ! [X31: $i] :
      ( ( k3_yellow_1 @ X31 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('10',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
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
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v1_xboole_0 @ X34 )
      | ~ ( v1_subset_1 @ X34 @ ( u1_struct_0 @ ( k3_yellow_1 @ X35 ) ) )
      | ~ ( v2_waybel_0 @ X34 @ ( k3_yellow_1 @ X35 ) )
      | ~ ( v13_waybel_0 @ X34 @ ( k3_yellow_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X35 ) ) ) )
      | ~ ( r2_hidden @ X36 @ X34 )
      | ~ ( v1_xboole_0 @ X36 )
      | ( v1_xboole_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t2_yellow19])).

thf('15',plain,(
    ! [X31: $i] :
      ( ( k3_yellow_1 @ X31 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('16',plain,(
    ! [X31: $i] :
      ( ( k3_yellow_1 @ X31 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('17',plain,(
    ! [X31: $i] :
      ( ( k3_yellow_1 @ X31 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('18',plain,(
    ! [X31: $i] :
      ( ( k3_yellow_1 @ X31 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('19',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v1_xboole_0 @ X34 )
      | ~ ( v1_subset_1 @ X34 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X35 ) ) ) )
      | ~ ( v2_waybel_0 @ X34 @ ( k3_lattice3 @ ( k1_lattice3 @ X35 ) ) )
      | ~ ( v13_waybel_0 @ X34 @ ( k3_lattice3 @ ( k1_lattice3 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X35 ) ) ) ) )
      | ~ ( r2_hidden @ X36 @ X34 )
      | ~ ( v1_xboole_0 @ X36 )
      | ( v1_xboole_0 @ X35 ) ) ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('21',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('22',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X31: $i] :
      ( ( k3_yellow_1 @ X31 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('24',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('26',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('29',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X31: $i] :
      ( ( k3_yellow_1 @ X31 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('31',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('36',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X31: $i] :
      ( ( k3_yellow_1 @ X31 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('38',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['20','27','34','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ ( sk_C_1 @ X0 @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ sk_B_1 @ ( k1_tarski @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( r1_xboole_0 @ sk_B_1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_xboole_0 @ sk_B_1 @ ( k1_tarski @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('46',plain,(
    ! [X30: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ sk_B_1 @ ( k1_tarski @ X0 ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ sk_B_1 @ ( k1_tarski @ X0 ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('50',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('51',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k3_xboole_0 @ X11 @ X14 ) )
      | ~ ( r1_xboole_0 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('54',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('58',plain,(
    ! [X21: $i] :
      ( r1_xboole_0 @ X21 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('59',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X22 ) @ X23 )
      | ~ ( r2_hidden @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('60',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('62',plain,(
    ! [X15: $i,X17: $i] :
      ( ( X15 = X17 )
      | ~ ( r1_tarski @ X17 @ X15 )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','63'])).

thf('65',plain,(
    ! [X21: $i] :
      ( r1_xboole_0 @ X21 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('67',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','63'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('70',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('72',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ X1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','73'])).

thf('75',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( v1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ X0 ) )
        = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['53','76'])).

thf('78',plain,(
    sk_B_1
 != ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
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

thf('80',plain,(
    ! [X32: $i,X33: $i] :
      ( ( v1_xboole_0 @ X32 )
      | ~ ( v2_waybel_0 @ X32 @ ( k3_yellow_1 @ ( k2_struct_0 @ X33 ) ) )
      | ~ ( v13_waybel_0 @ X32 @ ( k3_yellow_1 @ ( k2_struct_0 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X33 ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X33 ) ) ) @ X32 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X33 @ ( k3_yellow19 @ X33 @ ( k2_struct_0 @ X33 ) @ X32 ) ) )
      | ~ ( l1_struct_0 @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow19])).

thf('81',plain,(
    ! [X31: $i] :
      ( ( k3_yellow_1 @ X31 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('82',plain,(
    ! [X31: $i] :
      ( ( k3_yellow_1 @ X31 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('83',plain,(
    ! [X31: $i] :
      ( ( k3_yellow_1 @ X31 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('84',plain,(
    ! [X31: $i] :
      ( ( k3_yellow_1 @ X31 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('85',plain,(
    ! [X32: $i,X33: $i] :
      ( ( v1_xboole_0 @ X32 )
      | ~ ( v2_waybel_0 @ X32 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X33 ) ) ) )
      | ~ ( v13_waybel_0 @ X32 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X33 ) ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X33 ) ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X33 ) ) ) ) @ X32 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X33 @ ( k3_yellow19 @ X33 @ ( k2_struct_0 @ X33 ) @ X32 ) ) )
      | ~ ( l1_struct_0 @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(demod,[status(thm)],['80','81','82','83','84'])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['79','85'])).

thf('87',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('89',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['86','87','88','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('92',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) )
      | ( ( k7_subset_1 @ X27 @ X26 @ X28 )
        = ( k4_xboole_0 @ X26 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_1 @ X0 )
      = ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['90','93'])).

thf('95',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
    sk_B_1
 != ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['78','98'])).

thf('100',plain,
    ( ( sk_B_1 != sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','99'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('101',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('102',plain,
    ( ( sk_B_1 != sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,(
    $false ),
    inference(demod,[status(thm)],['0','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hPrJVvPzIa
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:49:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.36/1.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.36/1.58  % Solved by: fo/fo7.sh
% 1.36/1.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.36/1.58  % done 1619 iterations in 1.113s
% 1.36/1.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.36/1.58  % SZS output start Refutation
% 1.36/1.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.36/1.58  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.36/1.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.36/1.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.36/1.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.36/1.58  thf(sk_B_type, type, sk_B: $i > $i).
% 1.36/1.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.36/1.58  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 1.36/1.58  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 1.36/1.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.36/1.58  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.36/1.58  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.36/1.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.36/1.58  thf(sk_A_type, type, sk_A: $i).
% 1.36/1.58  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.36/1.58  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 1.36/1.58  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 1.36/1.58  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 1.36/1.58  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.36/1.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.36/1.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.36/1.58  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 1.36/1.58  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 1.36/1.58  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 1.36/1.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.36/1.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.36/1.58  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.36/1.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.36/1.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.36/1.58  thf(t15_yellow19, conjecture,
% 1.36/1.58    (![A:$i]:
% 1.36/1.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.36/1.58       ( ![B:$i]:
% 1.36/1.58         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 1.36/1.58             ( v1_subset_1 @
% 1.36/1.58               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 1.36/1.58             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 1.36/1.58             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 1.36/1.58             ( m1_subset_1 @
% 1.36/1.58               B @ 
% 1.36/1.58               ( k1_zfmisc_1 @
% 1.36/1.58                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 1.36/1.58           ( ( B ) =
% 1.36/1.58             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 1.36/1.58  thf(zf_stmt_0, negated_conjecture,
% 1.36/1.58    (~( ![A:$i]:
% 1.36/1.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.36/1.58          ( ![B:$i]:
% 1.36/1.58            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 1.36/1.58                ( v1_subset_1 @
% 1.36/1.58                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 1.36/1.58                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 1.36/1.58                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 1.36/1.58                ( m1_subset_1 @
% 1.36/1.58                  B @ 
% 1.36/1.58                  ( k1_zfmisc_1 @
% 1.36/1.58                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 1.36/1.58              ( ( B ) =
% 1.36/1.58                ( k2_yellow19 @
% 1.36/1.58                  A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) )),
% 1.36/1.58    inference('cnf.neg', [status(esa)], [t15_yellow19])).
% 1.36/1.58  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 1.36/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.58  thf(t3_xboole_0, axiom,
% 1.36/1.58    (![A:$i,B:$i]:
% 1.36/1.58     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.36/1.58            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.36/1.58       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.36/1.58            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.36/1.58  thf('1', plain,
% 1.36/1.58      (![X7 : $i, X8 : $i]:
% 1.36/1.58         ((r1_xboole_0 @ X7 @ X8) | (r2_hidden @ (sk_C_1 @ X8 @ X7) @ X8))),
% 1.36/1.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.36/1.58  thf(t17_zfmisc_1, axiom,
% 1.36/1.58    (![A:$i,B:$i]:
% 1.36/1.58     ( ( ( A ) != ( B ) ) =>
% 1.36/1.58       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 1.36/1.58  thf('2', plain,
% 1.36/1.58      (![X24 : $i, X25 : $i]:
% 1.36/1.58         ((r1_xboole_0 @ (k1_tarski @ X24) @ (k1_tarski @ X25))
% 1.36/1.58          | ((X24) = (X25)))),
% 1.36/1.58      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 1.36/1.58  thf(l24_zfmisc_1, axiom,
% 1.36/1.58    (![A:$i,B:$i]:
% 1.36/1.58     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 1.36/1.58  thf('3', plain,
% 1.36/1.58      (![X22 : $i, X23 : $i]:
% 1.36/1.58         (~ (r1_xboole_0 @ (k1_tarski @ X22) @ X23) | ~ (r2_hidden @ X22 @ X23))),
% 1.36/1.58      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 1.36/1.58  thf('4', plain,
% 1.36/1.58      (![X0 : $i, X1 : $i]:
% 1.36/1.58         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 1.36/1.58      inference('sup-', [status(thm)], ['2', '3'])).
% 1.36/1.58  thf('5', plain,
% 1.36/1.58      (![X0 : $i, X1 : $i]:
% 1.36/1.58         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 1.36/1.58          | ((sk_C_1 @ (k1_tarski @ X0) @ X1) = (X0)))),
% 1.36/1.58      inference('sup-', [status(thm)], ['1', '4'])).
% 1.36/1.58  thf('6', plain,
% 1.36/1.58      (![X7 : $i, X8 : $i]:
% 1.36/1.58         ((r1_xboole_0 @ X7 @ X8) | (r2_hidden @ (sk_C_1 @ X8 @ X7) @ X7))),
% 1.36/1.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.36/1.58  thf(d3_struct_0, axiom,
% 1.36/1.58    (![A:$i]:
% 1.36/1.58     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.36/1.58  thf('7', plain,
% 1.36/1.58      (![X29 : $i]:
% 1.36/1.58         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 1.36/1.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.36/1.58  thf('8', plain,
% 1.36/1.58      ((m1_subset_1 @ sk_B_1 @ 
% 1.36/1.58        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 1.36/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.58  thf(d2_yellow_1, axiom,
% 1.36/1.58    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 1.36/1.58  thf('9', plain,
% 1.36/1.58      (![X31 : $i]: ((k3_yellow_1 @ X31) = (k3_lattice3 @ (k1_lattice3 @ X31)))),
% 1.36/1.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.36/1.58  thf('10', plain,
% 1.36/1.58      ((m1_subset_1 @ sk_B_1 @ 
% 1.36/1.58        (k1_zfmisc_1 @ 
% 1.36/1.58         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 1.36/1.58      inference('demod', [status(thm)], ['8', '9'])).
% 1.36/1.58  thf('11', plain,
% 1.36/1.58      (((m1_subset_1 @ sk_B_1 @ 
% 1.36/1.58         (k1_zfmisc_1 @ 
% 1.36/1.58          (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))
% 1.36/1.58        | ~ (l1_struct_0 @ sk_A))),
% 1.36/1.58      inference('sup+', [status(thm)], ['7', '10'])).
% 1.36/1.58  thf('12', plain, ((l1_struct_0 @ sk_A)),
% 1.36/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.58  thf('13', plain,
% 1.36/1.58      ((m1_subset_1 @ sk_B_1 @ 
% 1.36/1.58        (k1_zfmisc_1 @ 
% 1.36/1.58         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 1.36/1.58      inference('demod', [status(thm)], ['11', '12'])).
% 1.36/1.58  thf(t2_yellow19, axiom,
% 1.36/1.58    (![A:$i]:
% 1.36/1.58     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.36/1.58       ( ![B:$i]:
% 1.36/1.58         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 1.36/1.58             ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 1.36/1.58             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 1.36/1.58             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 1.36/1.58             ( m1_subset_1 @
% 1.36/1.58               B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 1.36/1.58           ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ))).
% 1.36/1.58  thf('14', plain,
% 1.36/1.58      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.36/1.58         ((v1_xboole_0 @ X34)
% 1.36/1.58          | ~ (v1_subset_1 @ X34 @ (u1_struct_0 @ (k3_yellow_1 @ X35)))
% 1.36/1.58          | ~ (v2_waybel_0 @ X34 @ (k3_yellow_1 @ X35))
% 1.36/1.58          | ~ (v13_waybel_0 @ X34 @ (k3_yellow_1 @ X35))
% 1.36/1.58          | ~ (m1_subset_1 @ X34 @ 
% 1.36/1.58               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X35))))
% 1.36/1.58          | ~ (r2_hidden @ X36 @ X34)
% 1.36/1.58          | ~ (v1_xboole_0 @ X36)
% 1.36/1.58          | (v1_xboole_0 @ X35))),
% 1.36/1.58      inference('cnf', [status(esa)], [t2_yellow19])).
% 1.36/1.58  thf('15', plain,
% 1.36/1.58      (![X31 : $i]: ((k3_yellow_1 @ X31) = (k3_lattice3 @ (k1_lattice3 @ X31)))),
% 1.36/1.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.36/1.58  thf('16', plain,
% 1.36/1.58      (![X31 : $i]: ((k3_yellow_1 @ X31) = (k3_lattice3 @ (k1_lattice3 @ X31)))),
% 1.36/1.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.36/1.58  thf('17', plain,
% 1.36/1.58      (![X31 : $i]: ((k3_yellow_1 @ X31) = (k3_lattice3 @ (k1_lattice3 @ X31)))),
% 1.36/1.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.36/1.58  thf('18', plain,
% 1.36/1.58      (![X31 : $i]: ((k3_yellow_1 @ X31) = (k3_lattice3 @ (k1_lattice3 @ X31)))),
% 1.36/1.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.36/1.58  thf('19', plain,
% 1.36/1.58      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.36/1.58         ((v1_xboole_0 @ X34)
% 1.36/1.58          | ~ (v1_subset_1 @ X34 @ 
% 1.36/1.58               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X35))))
% 1.36/1.58          | ~ (v2_waybel_0 @ X34 @ (k3_lattice3 @ (k1_lattice3 @ X35)))
% 1.36/1.58          | ~ (v13_waybel_0 @ X34 @ (k3_lattice3 @ (k1_lattice3 @ X35)))
% 1.36/1.58          | ~ (m1_subset_1 @ X34 @ 
% 1.36/1.58               (k1_zfmisc_1 @ 
% 1.36/1.58                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X35)))))
% 1.36/1.58          | ~ (r2_hidden @ X36 @ X34)
% 1.36/1.58          | ~ (v1_xboole_0 @ X36)
% 1.36/1.58          | (v1_xboole_0 @ X35))),
% 1.36/1.58      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 1.36/1.58  thf('20', plain,
% 1.36/1.58      (![X0 : $i]:
% 1.36/1.58         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.36/1.58          | ~ (v1_xboole_0 @ X0)
% 1.36/1.58          | ~ (r2_hidden @ X0 @ sk_B_1)
% 1.36/1.58          | ~ (v13_waybel_0 @ sk_B_1 @ 
% 1.36/1.58               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 1.36/1.58          | ~ (v2_waybel_0 @ sk_B_1 @ 
% 1.36/1.58               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 1.36/1.58          | ~ (v1_subset_1 @ sk_B_1 @ 
% 1.36/1.58               (u1_struct_0 @ 
% 1.36/1.58                (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))
% 1.36/1.58          | (v1_xboole_0 @ sk_B_1))),
% 1.36/1.58      inference('sup-', [status(thm)], ['13', '19'])).
% 1.36/1.58  thf('21', plain,
% 1.36/1.58      (![X29 : $i]:
% 1.36/1.58         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 1.36/1.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.36/1.58  thf('22', plain,
% 1.36/1.58      ((v13_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 1.36/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.58  thf('23', plain,
% 1.36/1.58      (![X31 : $i]: ((k3_yellow_1 @ X31) = (k3_lattice3 @ (k1_lattice3 @ X31)))),
% 1.36/1.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.36/1.58  thf('24', plain,
% 1.36/1.58      ((v13_waybel_0 @ sk_B_1 @ 
% 1.36/1.58        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 1.36/1.58      inference('demod', [status(thm)], ['22', '23'])).
% 1.36/1.58  thf('25', plain,
% 1.36/1.58      (((v13_waybel_0 @ sk_B_1 @ 
% 1.36/1.58         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 1.36/1.58        | ~ (l1_struct_0 @ sk_A))),
% 1.36/1.58      inference('sup+', [status(thm)], ['21', '24'])).
% 1.36/1.58  thf('26', plain, ((l1_struct_0 @ sk_A)),
% 1.36/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.58  thf('27', plain,
% 1.36/1.58      ((v13_waybel_0 @ sk_B_1 @ 
% 1.36/1.58        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 1.36/1.58      inference('demod', [status(thm)], ['25', '26'])).
% 1.36/1.58  thf('28', plain,
% 1.36/1.58      (![X29 : $i]:
% 1.36/1.58         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 1.36/1.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.36/1.58  thf('29', plain,
% 1.36/1.58      ((v2_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 1.36/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.58  thf('30', plain,
% 1.36/1.58      (![X31 : $i]: ((k3_yellow_1 @ X31) = (k3_lattice3 @ (k1_lattice3 @ X31)))),
% 1.36/1.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.36/1.58  thf('31', plain,
% 1.36/1.58      ((v2_waybel_0 @ sk_B_1 @ 
% 1.36/1.58        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 1.36/1.58      inference('demod', [status(thm)], ['29', '30'])).
% 1.36/1.58  thf('32', plain,
% 1.36/1.58      (((v2_waybel_0 @ sk_B_1 @ 
% 1.36/1.58         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 1.36/1.58        | ~ (l1_struct_0 @ sk_A))),
% 1.36/1.58      inference('sup+', [status(thm)], ['28', '31'])).
% 1.36/1.58  thf('33', plain, ((l1_struct_0 @ sk_A)),
% 1.36/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.58  thf('34', plain,
% 1.36/1.58      ((v2_waybel_0 @ sk_B_1 @ 
% 1.36/1.58        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 1.36/1.58      inference('demod', [status(thm)], ['32', '33'])).
% 1.36/1.58  thf('35', plain,
% 1.36/1.58      (![X29 : $i]:
% 1.36/1.58         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 1.36/1.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.36/1.58  thf('36', plain,
% 1.36/1.58      ((v1_subset_1 @ sk_B_1 @ 
% 1.36/1.58        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 1.36/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.58  thf('37', plain,
% 1.36/1.58      (![X31 : $i]: ((k3_yellow_1 @ X31) = (k3_lattice3 @ (k1_lattice3 @ X31)))),
% 1.36/1.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.36/1.58  thf('38', plain,
% 1.36/1.58      ((v1_subset_1 @ sk_B_1 @ 
% 1.36/1.58        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 1.36/1.58      inference('demod', [status(thm)], ['36', '37'])).
% 1.36/1.58  thf('39', plain,
% 1.36/1.58      (((v1_subset_1 @ sk_B_1 @ 
% 1.36/1.58         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))
% 1.36/1.58        | ~ (l1_struct_0 @ sk_A))),
% 1.36/1.58      inference('sup+', [status(thm)], ['35', '38'])).
% 1.36/1.58  thf('40', plain, ((l1_struct_0 @ sk_A)),
% 1.36/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.58  thf('41', plain,
% 1.36/1.58      ((v1_subset_1 @ sk_B_1 @ 
% 1.36/1.58        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 1.36/1.58      inference('demod', [status(thm)], ['39', '40'])).
% 1.36/1.58  thf('42', plain,
% 1.36/1.58      (![X0 : $i]:
% 1.36/1.58         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.36/1.58          | ~ (v1_xboole_0 @ X0)
% 1.36/1.58          | ~ (r2_hidden @ X0 @ sk_B_1)
% 1.36/1.58          | (v1_xboole_0 @ sk_B_1))),
% 1.36/1.58      inference('demod', [status(thm)], ['20', '27', '34', '41'])).
% 1.36/1.58  thf('43', plain,
% 1.36/1.58      (![X0 : $i]:
% 1.36/1.58         ((r1_xboole_0 @ sk_B_1 @ X0)
% 1.36/1.58          | (v1_xboole_0 @ sk_B_1)
% 1.36/1.58          | ~ (v1_xboole_0 @ (sk_C_1 @ X0 @ sk_B_1))
% 1.36/1.58          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.36/1.58      inference('sup-', [status(thm)], ['6', '42'])).
% 1.36/1.58  thf('44', plain,
% 1.36/1.58      (![X0 : $i]:
% 1.36/1.58         (~ (v1_xboole_0 @ X0)
% 1.36/1.58          | (r1_xboole_0 @ sk_B_1 @ (k1_tarski @ X0))
% 1.36/1.58          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.36/1.58          | (v1_xboole_0 @ sk_B_1)
% 1.36/1.58          | (r1_xboole_0 @ sk_B_1 @ (k1_tarski @ X0)))),
% 1.36/1.58      inference('sup-', [status(thm)], ['5', '43'])).
% 1.36/1.58  thf('45', plain,
% 1.36/1.58      (![X0 : $i]:
% 1.36/1.58         ((v1_xboole_0 @ sk_B_1)
% 1.36/1.58          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.36/1.58          | (r1_xboole_0 @ sk_B_1 @ (k1_tarski @ X0))
% 1.36/1.58          | ~ (v1_xboole_0 @ X0))),
% 1.36/1.58      inference('simplify', [status(thm)], ['44'])).
% 1.36/1.58  thf(fc2_struct_0, axiom,
% 1.36/1.58    (![A:$i]:
% 1.36/1.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.36/1.58       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.36/1.58  thf('46', plain,
% 1.36/1.58      (![X30 : $i]:
% 1.36/1.58         (~ (v1_xboole_0 @ (u1_struct_0 @ X30))
% 1.36/1.58          | ~ (l1_struct_0 @ X30)
% 1.36/1.58          | (v2_struct_0 @ X30))),
% 1.36/1.58      inference('cnf', [status(esa)], [fc2_struct_0])).
% 1.36/1.58  thf('47', plain,
% 1.36/1.58      (![X0 : $i]:
% 1.36/1.58         (~ (v1_xboole_0 @ X0)
% 1.36/1.58          | (r1_xboole_0 @ sk_B_1 @ (k1_tarski @ X0))
% 1.36/1.58          | (v1_xboole_0 @ sk_B_1)
% 1.36/1.58          | (v2_struct_0 @ sk_A)
% 1.36/1.58          | ~ (l1_struct_0 @ sk_A))),
% 1.36/1.58      inference('sup-', [status(thm)], ['45', '46'])).
% 1.36/1.58  thf('48', plain, ((l1_struct_0 @ sk_A)),
% 1.36/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.58  thf('49', plain,
% 1.36/1.58      (![X0 : $i]:
% 1.36/1.58         (~ (v1_xboole_0 @ X0)
% 1.36/1.58          | (r1_xboole_0 @ sk_B_1 @ (k1_tarski @ X0))
% 1.36/1.58          | (v1_xboole_0 @ sk_B_1)
% 1.36/1.58          | (v2_struct_0 @ sk_A))),
% 1.36/1.58      inference('demod', [status(thm)], ['47', '48'])).
% 1.36/1.58  thf(d1_xboole_0, axiom,
% 1.36/1.58    (![A:$i]:
% 1.36/1.58     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.36/1.58  thf('50', plain,
% 1.36/1.58      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.36/1.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.36/1.58  thf(t4_xboole_0, axiom,
% 1.36/1.58    (![A:$i,B:$i]:
% 1.36/1.58     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.36/1.58            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.36/1.58       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.36/1.58            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.36/1.58  thf('51', plain,
% 1.36/1.58      (![X11 : $i, X13 : $i, X14 : $i]:
% 1.36/1.58         (~ (r2_hidden @ X13 @ (k3_xboole_0 @ X11 @ X14))
% 1.36/1.58          | ~ (r1_xboole_0 @ X11 @ X14))),
% 1.36/1.58      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.36/1.58  thf('52', plain,
% 1.36/1.58      (![X0 : $i, X1 : $i]:
% 1.36/1.58         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.36/1.58      inference('sup-', [status(thm)], ['50', '51'])).
% 1.36/1.58  thf('53', plain,
% 1.36/1.58      (![X0 : $i]:
% 1.36/1.58         ((v2_struct_0 @ sk_A)
% 1.36/1.58          | (v1_xboole_0 @ sk_B_1)
% 1.36/1.58          | ~ (v1_xboole_0 @ X0)
% 1.36/1.58          | (v1_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ X0))))),
% 1.36/1.58      inference('sup-', [status(thm)], ['49', '52'])).
% 1.36/1.58  thf(d3_tarski, axiom,
% 1.36/1.58    (![A:$i,B:$i]:
% 1.36/1.58     ( ( r1_tarski @ A @ B ) <=>
% 1.36/1.58       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.36/1.58  thf('54', plain,
% 1.36/1.58      (![X4 : $i, X6 : $i]:
% 1.36/1.58         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 1.36/1.58      inference('cnf', [status(esa)], [d3_tarski])).
% 1.36/1.58  thf('55', plain,
% 1.36/1.58      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.36/1.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.36/1.58  thf('56', plain,
% 1.36/1.58      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.36/1.58      inference('sup-', [status(thm)], ['54', '55'])).
% 1.36/1.58  thf('57', plain,
% 1.36/1.58      (![X4 : $i, X6 : $i]:
% 1.36/1.58         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 1.36/1.58      inference('cnf', [status(esa)], [d3_tarski])).
% 1.36/1.58  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 1.36/1.58  thf('58', plain, (![X21 : $i]: (r1_xboole_0 @ X21 @ k1_xboole_0)),
% 1.36/1.58      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.36/1.58  thf('59', plain,
% 1.36/1.58      (![X22 : $i, X23 : $i]:
% 1.36/1.58         (~ (r1_xboole_0 @ (k1_tarski @ X22) @ X23) | ~ (r2_hidden @ X22 @ X23))),
% 1.36/1.58      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 1.36/1.58  thf('60', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.36/1.58      inference('sup-', [status(thm)], ['58', '59'])).
% 1.36/1.58  thf('61', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.36/1.58      inference('sup-', [status(thm)], ['57', '60'])).
% 1.36/1.58  thf(d10_xboole_0, axiom,
% 1.36/1.58    (![A:$i,B:$i]:
% 1.36/1.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.36/1.58  thf('62', plain,
% 1.36/1.58      (![X15 : $i, X17 : $i]:
% 1.36/1.58         (((X15) = (X17))
% 1.36/1.58          | ~ (r1_tarski @ X17 @ X15)
% 1.36/1.58          | ~ (r1_tarski @ X15 @ X17))),
% 1.36/1.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.36/1.58  thf('63', plain,
% 1.36/1.58      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.36/1.58      inference('sup-', [status(thm)], ['61', '62'])).
% 1.36/1.58  thf('64', plain,
% 1.36/1.58      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 1.36/1.58      inference('sup-', [status(thm)], ['56', '63'])).
% 1.36/1.58  thf('65', plain, (![X21 : $i]: (r1_xboole_0 @ X21 @ k1_xboole_0)),
% 1.36/1.58      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.36/1.58  thf('66', plain,
% 1.36/1.58      (![X0 : $i, X1 : $i]:
% 1.36/1.58         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.36/1.58      inference('sup-', [status(thm)], ['50', '51'])).
% 1.36/1.58  thf('67', plain,
% 1.36/1.58      (![X0 : $i]: (v1_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.36/1.58      inference('sup-', [status(thm)], ['65', '66'])).
% 1.36/1.58  thf('68', plain,
% 1.36/1.58      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 1.36/1.58      inference('sup-', [status(thm)], ['56', '63'])).
% 1.36/1.58  thf('69', plain,
% 1.36/1.58      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.36/1.58      inference('sup-', [status(thm)], ['67', '68'])).
% 1.36/1.58  thf(t100_xboole_1, axiom,
% 1.36/1.58    (![A:$i,B:$i]:
% 1.36/1.58     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.36/1.58  thf('70', plain,
% 1.36/1.58      (![X18 : $i, X19 : $i]:
% 1.36/1.58         ((k4_xboole_0 @ X18 @ X19)
% 1.36/1.58           = (k5_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19)))),
% 1.36/1.58      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.36/1.58  thf('71', plain,
% 1.36/1.58      (![X0 : $i]:
% 1.36/1.58         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.36/1.58      inference('sup+', [status(thm)], ['69', '70'])).
% 1.36/1.58  thf(t3_boole, axiom,
% 1.36/1.58    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.36/1.58  thf('72', plain, (![X20 : $i]: ((k4_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 1.36/1.58      inference('cnf', [status(esa)], [t3_boole])).
% 1.36/1.58  thf('73', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.36/1.58      inference('sup+', [status(thm)], ['71', '72'])).
% 1.36/1.58  thf('74', plain,
% 1.36/1.58      (![X0 : $i, X1 : $i]:
% 1.36/1.58         (((k5_xboole_0 @ X1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 1.36/1.58      inference('sup+', [status(thm)], ['64', '73'])).
% 1.36/1.58  thf('75', plain,
% 1.36/1.58      (![X18 : $i, X19 : $i]:
% 1.36/1.58         ((k4_xboole_0 @ X18 @ X19)
% 1.36/1.58           = (k5_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19)))),
% 1.36/1.58      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.36/1.58  thf('76', plain,
% 1.36/1.58      (![X0 : $i, X1 : $i]:
% 1.36/1.58         (((k4_xboole_0 @ X0 @ X1) = (X0))
% 1.36/1.58          | ~ (v1_xboole_0 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.36/1.58      inference('sup+', [status(thm)], ['74', '75'])).
% 1.36/1.58  thf('77', plain,
% 1.36/1.58      (![X0 : $i]:
% 1.36/1.58         (~ (v1_xboole_0 @ X0)
% 1.36/1.58          | (v1_xboole_0 @ sk_B_1)
% 1.36/1.58          | (v2_struct_0 @ sk_A)
% 1.36/1.58          | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ X0)) = (sk_B_1)))),
% 1.36/1.58      inference('sup-', [status(thm)], ['53', '76'])).
% 1.36/1.58  thf('78', plain,
% 1.36/1.58      (((sk_B_1)
% 1.36/1.58         != (k2_yellow19 @ sk_A @ 
% 1.36/1.58             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 1.36/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.58  thf('79', plain,
% 1.36/1.58      ((m1_subset_1 @ sk_B_1 @ 
% 1.36/1.58        (k1_zfmisc_1 @ 
% 1.36/1.58         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 1.36/1.58      inference('demod', [status(thm)], ['8', '9'])).
% 1.36/1.58  thf(t14_yellow19, axiom,
% 1.36/1.58    (![A:$i]:
% 1.36/1.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.36/1.58       ( ![B:$i]:
% 1.36/1.58         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 1.36/1.58             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 1.36/1.58             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 1.36/1.58             ( m1_subset_1 @
% 1.36/1.58               B @ 
% 1.36/1.58               ( k1_zfmisc_1 @
% 1.36/1.58                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 1.36/1.58           ( ( k7_subset_1 @
% 1.36/1.58               ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ 
% 1.36/1.58               ( k1_tarski @ k1_xboole_0 ) ) =
% 1.36/1.58             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 1.36/1.58  thf('80', plain,
% 1.36/1.58      (![X32 : $i, X33 : $i]:
% 1.36/1.58         ((v1_xboole_0 @ X32)
% 1.36/1.58          | ~ (v2_waybel_0 @ X32 @ (k3_yellow_1 @ (k2_struct_0 @ X33)))
% 1.36/1.58          | ~ (v13_waybel_0 @ X32 @ (k3_yellow_1 @ (k2_struct_0 @ X33)))
% 1.36/1.58          | ~ (m1_subset_1 @ X32 @ 
% 1.36/1.58               (k1_zfmisc_1 @ 
% 1.36/1.58                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X33)))))
% 1.36/1.58          | ((k7_subset_1 @ 
% 1.36/1.58              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X33))) @ X32 @ 
% 1.36/1.58              (k1_tarski @ k1_xboole_0))
% 1.36/1.58              = (k2_yellow19 @ X33 @ 
% 1.36/1.58                 (k3_yellow19 @ X33 @ (k2_struct_0 @ X33) @ X32)))
% 1.36/1.58          | ~ (l1_struct_0 @ X33)
% 1.36/1.58          | (v2_struct_0 @ X33))),
% 1.36/1.58      inference('cnf', [status(esa)], [t14_yellow19])).
% 1.36/1.58  thf('81', plain,
% 1.36/1.58      (![X31 : $i]: ((k3_yellow_1 @ X31) = (k3_lattice3 @ (k1_lattice3 @ X31)))),
% 1.36/1.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.36/1.58  thf('82', plain,
% 1.36/1.58      (![X31 : $i]: ((k3_yellow_1 @ X31) = (k3_lattice3 @ (k1_lattice3 @ X31)))),
% 1.36/1.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.36/1.58  thf('83', plain,
% 1.36/1.58      (![X31 : $i]: ((k3_yellow_1 @ X31) = (k3_lattice3 @ (k1_lattice3 @ X31)))),
% 1.36/1.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.36/1.58  thf('84', plain,
% 1.36/1.58      (![X31 : $i]: ((k3_yellow_1 @ X31) = (k3_lattice3 @ (k1_lattice3 @ X31)))),
% 1.36/1.58      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.36/1.58  thf('85', plain,
% 1.36/1.58      (![X32 : $i, X33 : $i]:
% 1.36/1.58         ((v1_xboole_0 @ X32)
% 1.36/1.58          | ~ (v2_waybel_0 @ X32 @ 
% 1.36/1.58               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X33))))
% 1.36/1.58          | ~ (v13_waybel_0 @ X32 @ 
% 1.36/1.58               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X33))))
% 1.36/1.58          | ~ (m1_subset_1 @ X32 @ 
% 1.36/1.58               (k1_zfmisc_1 @ 
% 1.36/1.58                (u1_struct_0 @ 
% 1.36/1.58                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X33))))))
% 1.36/1.58          | ((k7_subset_1 @ 
% 1.36/1.58              (u1_struct_0 @ 
% 1.36/1.58               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X33)))) @ 
% 1.36/1.58              X32 @ (k1_tarski @ k1_xboole_0))
% 1.36/1.58              = (k2_yellow19 @ X33 @ 
% 1.36/1.58                 (k3_yellow19 @ X33 @ (k2_struct_0 @ X33) @ X32)))
% 1.36/1.58          | ~ (l1_struct_0 @ X33)
% 1.36/1.58          | (v2_struct_0 @ X33))),
% 1.36/1.58      inference('demod', [status(thm)], ['80', '81', '82', '83', '84'])).
% 1.36/1.58  thf('86', plain,
% 1.36/1.58      (((v2_struct_0 @ sk_A)
% 1.36/1.58        | ~ (l1_struct_0 @ sk_A)
% 1.36/1.58        | ((k7_subset_1 @ 
% 1.36/1.58            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 1.36/1.58            sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 1.36/1.58            = (k2_yellow19 @ sk_A @ 
% 1.36/1.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 1.36/1.58        | ~ (v13_waybel_0 @ sk_B_1 @ 
% 1.36/1.58             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 1.36/1.58        | ~ (v2_waybel_0 @ sk_B_1 @ 
% 1.36/1.58             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 1.36/1.58        | (v1_xboole_0 @ sk_B_1))),
% 1.36/1.58      inference('sup-', [status(thm)], ['79', '85'])).
% 1.36/1.58  thf('87', plain, ((l1_struct_0 @ sk_A)),
% 1.36/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.58  thf('88', plain,
% 1.36/1.58      ((v13_waybel_0 @ sk_B_1 @ 
% 1.36/1.58        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 1.36/1.58      inference('demod', [status(thm)], ['22', '23'])).
% 1.36/1.58  thf('89', plain,
% 1.36/1.58      ((v2_waybel_0 @ sk_B_1 @ 
% 1.36/1.58        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 1.36/1.58      inference('demod', [status(thm)], ['29', '30'])).
% 1.36/1.58  thf('90', plain,
% 1.36/1.58      (((v2_struct_0 @ sk_A)
% 1.36/1.58        | ((k7_subset_1 @ 
% 1.36/1.58            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 1.36/1.58            sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 1.36/1.58            = (k2_yellow19 @ sk_A @ 
% 1.36/1.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 1.36/1.58        | (v1_xboole_0 @ sk_B_1))),
% 1.36/1.58      inference('demod', [status(thm)], ['86', '87', '88', '89'])).
% 1.36/1.58  thf('91', plain,
% 1.36/1.58      ((m1_subset_1 @ sk_B_1 @ 
% 1.36/1.58        (k1_zfmisc_1 @ 
% 1.36/1.58         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 1.36/1.58      inference('demod', [status(thm)], ['8', '9'])).
% 1.36/1.58  thf(redefinition_k7_subset_1, axiom,
% 1.36/1.58    (![A:$i,B:$i,C:$i]:
% 1.36/1.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.36/1.58       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.36/1.58  thf('92', plain,
% 1.36/1.58      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.36/1.58         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27))
% 1.36/1.58          | ((k7_subset_1 @ X27 @ X26 @ X28) = (k4_xboole_0 @ X26 @ X28)))),
% 1.36/1.58      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.36/1.58  thf('93', plain,
% 1.36/1.58      (![X0 : $i]:
% 1.36/1.58         ((k7_subset_1 @ 
% 1.36/1.58           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 1.36/1.58           sk_B_1 @ X0) = (k4_xboole_0 @ sk_B_1 @ X0))),
% 1.36/1.58      inference('sup-', [status(thm)], ['91', '92'])).
% 1.36/1.58  thf('94', plain,
% 1.36/1.58      (((v2_struct_0 @ sk_A)
% 1.36/1.58        | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 1.36/1.58            = (k2_yellow19 @ sk_A @ 
% 1.36/1.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 1.36/1.58        | (v1_xboole_0 @ sk_B_1))),
% 1.36/1.58      inference('demod', [status(thm)], ['90', '93'])).
% 1.36/1.58  thf('95', plain, (~ (v2_struct_0 @ sk_A)),
% 1.36/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.58  thf('96', plain,
% 1.36/1.58      (((v1_xboole_0 @ sk_B_1)
% 1.36/1.58        | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 1.36/1.58            = (k2_yellow19 @ sk_A @ 
% 1.36/1.58               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))),
% 1.36/1.58      inference('clc', [status(thm)], ['94', '95'])).
% 1.36/1.58  thf('97', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.36/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.58  thf('98', plain,
% 1.36/1.58      (((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 1.36/1.58         = (k2_yellow19 @ sk_A @ 
% 1.36/1.58            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 1.36/1.58      inference('clc', [status(thm)], ['96', '97'])).
% 1.36/1.58  thf('99', plain,
% 1.36/1.58      (((sk_B_1) != (k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0)))),
% 1.36/1.58      inference('demod', [status(thm)], ['78', '98'])).
% 1.36/1.58  thf('100', plain,
% 1.36/1.58      ((((sk_B_1) != (sk_B_1))
% 1.36/1.58        | (v2_struct_0 @ sk_A)
% 1.36/1.58        | (v1_xboole_0 @ sk_B_1)
% 1.36/1.58        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.36/1.58      inference('sup-', [status(thm)], ['77', '99'])).
% 1.36/1.58  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.36/1.58  thf('101', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.36/1.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.36/1.58  thf('102', plain,
% 1.36/1.58      ((((sk_B_1) != (sk_B_1)) | (v2_struct_0 @ sk_A) | (v1_xboole_0 @ sk_B_1))),
% 1.36/1.58      inference('demod', [status(thm)], ['100', '101'])).
% 1.36/1.58  thf('103', plain, (((v1_xboole_0 @ sk_B_1) | (v2_struct_0 @ sk_A))),
% 1.36/1.58      inference('simplify', [status(thm)], ['102'])).
% 1.36/1.58  thf('104', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.36/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.58  thf('105', plain, ((v2_struct_0 @ sk_A)),
% 1.36/1.58      inference('clc', [status(thm)], ['103', '104'])).
% 1.36/1.58  thf('106', plain, ($false), inference('demod', [status(thm)], ['0', '105'])).
% 1.36/1.58  
% 1.36/1.58  % SZS output end Refutation
% 1.36/1.58  
% 1.36/1.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
