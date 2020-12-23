%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Itqls4VG4K

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:44 EST 2020

% Result     : Theorem 1.02s
% Output     : Refutation 1.02s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 218 expanded)
%              Number of leaves         :   38 (  85 expanded)
%              Depth                    :   19
%              Number of atoms          : 1132 (2875 expanded)
%              Number of equality atoms :   51 ( 119 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C @ X10 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i,X23: $i] :
      ( ( r2_hidden @ X20 @ ( k4_xboole_0 @ X21 @ ( k1_tarski @ X23 ) ) )
      | ( X20 = X23 )
      | ~ ( r2_hidden @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( ( sk_C @ X1 @ X0 )
        = X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('4',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ( X8
        = ( k4_xboole_0 @ X4 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('6',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ( X8
        = ( k4_xboole_0 @ X4 @ X5 ) )
      | ~ ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf('13',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( X20 != X22 )
      | ~ ( r2_hidden @ X20 @ ( k4_xboole_0 @ X21 @ ( k1_tarski @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('14',plain,(
    ! [X21: $i,X22: $i] :
      ~ ( r2_hidden @ X22 @ ( k4_xboole_0 @ X21 @ ( k1_tarski @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','16'])).

thf('18',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C @ X10 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('19',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('20',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('21',plain,(
    ! [X31: $i] :
      ( ( k3_yellow_1 @ X31 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('22',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

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

thf('26',plain,(
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

thf('27',plain,(
    ! [X31: $i] :
      ( ( k3_yellow_1 @ X31 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('28',plain,(
    ! [X31: $i] :
      ( ( k3_yellow_1 @ X31 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('29',plain,(
    ! [X31: $i] :
      ( ( k3_yellow_1 @ X31 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('30',plain,(
    ! [X31: $i] :
      ( ( k3_yellow_1 @ X31 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('31',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v1_xboole_0 @ X34 )
      | ~ ( v1_subset_1 @ X34 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X35 ) ) ) )
      | ~ ( v2_waybel_0 @ X34 @ ( k3_lattice3 @ ( k1_lattice3 @ X35 ) ) )
      | ~ ( v13_waybel_0 @ X34 @ ( k3_lattice3 @ ( k1_lattice3 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X35 ) ) ) ) )
      | ~ ( r2_hidden @ X36 @ X34 )
      | ~ ( v1_xboole_0 @ X36 )
      | ( v1_xboole_0 @ X35 ) ) ),
    inference(demod,[status(thm)],['26','27','28','29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('34',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X31: $i] :
      ( ( k3_yellow_1 @ X31 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('36',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('41',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X31: $i] :
      ( ( k3_yellow_1 @ X31 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('43',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf('45',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('48',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X31: $i] :
      ( ( k3_yellow_1 @ X31 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('50',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['47','50'])).

thf('52',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['32','39','46','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ ( sk_C @ sk_B_1 @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['17','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('58',plain,(
    ! [X30: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C @ X10 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('63',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C @ X10 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('64',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ sk_B_1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','67'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('69',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ X0 ) )
        = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    sk_B_1
 != ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

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

thf('73',plain,(
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

thf('74',plain,(
    ! [X31: $i] :
      ( ( k3_yellow_1 @ X31 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('75',plain,(
    ! [X31: $i] :
      ( ( k3_yellow_1 @ X31 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('76',plain,(
    ! [X31: $i] :
      ( ( k3_yellow_1 @ X31 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('77',plain,(
    ! [X31: $i] :
      ( ( k3_yellow_1 @ X31 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('78',plain,(
    ! [X32: $i,X33: $i] :
      ( ( v1_xboole_0 @ X32 )
      | ~ ( v2_waybel_0 @ X32 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X33 ) ) ) )
      | ~ ( v13_waybel_0 @ X32 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X33 ) ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X33 ) ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X33 ) ) ) ) @ X32 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X33 @ ( k3_yellow19 @ X33 @ ( k2_struct_0 @ X33 ) @ X32 ) ) )
      | ~ ( l1_struct_0 @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(demod,[status(thm)],['73','74','75','76','77'])).

thf('79',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['72','78'])).

thf('80',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('82',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ( ( k7_subset_1 @ X25 @ X24 @ X26 )
        = ( k4_xboole_0 @ X24 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) @ sk_B_1 @ X0 )
      = ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('85',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['79','80','83','84','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    sk_B_1
 != ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['71','90'])).

thf('92',plain,
    ( ( sk_B_1 != sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','91'])).

thf('93',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('94',plain,
    ( ( sk_B_1 != sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    $false ),
    inference(demod,[status(thm)],['0','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Itqls4VG4K
% 0.13/0.36  % Computer   : n024.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 09:19:36 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 1.02/1.21  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.02/1.21  % Solved by: fo/fo7.sh
% 1.02/1.21  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.02/1.21  % done 1220 iterations in 0.725s
% 1.02/1.21  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.02/1.21  % SZS output start Refutation
% 1.02/1.21  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.02/1.21  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.02/1.21  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.02/1.21  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.02/1.21  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 1.02/1.21  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.02/1.21  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 1.02/1.21  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.02/1.21  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 1.02/1.21  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.02/1.21  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.02/1.21  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.02/1.21  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.02/1.21  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.02/1.21  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 1.02/1.21  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 1.02/1.21  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 1.02/1.21  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 1.02/1.21  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.02/1.21  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.02/1.21  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 1.02/1.21  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.02/1.21  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.02/1.21  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.02/1.21  thf(sk_A_type, type, sk_A: $i).
% 1.02/1.21  thf(t15_yellow19, conjecture,
% 1.02/1.21    (![A:$i]:
% 1.02/1.21     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.02/1.21       ( ![B:$i]:
% 1.02/1.21         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 1.02/1.21             ( v1_subset_1 @
% 1.02/1.21               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 1.02/1.21             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 1.02/1.21             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 1.02/1.21             ( m1_subset_1 @
% 1.02/1.21               B @ 
% 1.02/1.21               ( k1_zfmisc_1 @
% 1.02/1.21                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 1.02/1.21           ( ( B ) =
% 1.02/1.21             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 1.02/1.21  thf(zf_stmt_0, negated_conjecture,
% 1.02/1.21    (~( ![A:$i]:
% 1.02/1.21        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.02/1.21          ( ![B:$i]:
% 1.02/1.21            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 1.02/1.21                ( v1_subset_1 @
% 1.02/1.21                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 1.02/1.21                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 1.02/1.21                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 1.02/1.21                ( m1_subset_1 @
% 1.02/1.21                  B @ 
% 1.02/1.21                  ( k1_zfmisc_1 @
% 1.02/1.21                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 1.02/1.21              ( ( B ) =
% 1.02/1.21                ( k2_yellow19 @
% 1.02/1.21                  A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) )),
% 1.02/1.21    inference('cnf.neg', [status(esa)], [t15_yellow19])).
% 1.02/1.21  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf(t3_xboole_0, axiom,
% 1.02/1.21    (![A:$i,B:$i]:
% 1.02/1.21     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.02/1.21            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.02/1.21       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.02/1.21            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.02/1.21  thf('1', plain,
% 1.02/1.21      (![X9 : $i, X10 : $i]:
% 1.02/1.21         ((r1_xboole_0 @ X9 @ X10) | (r2_hidden @ (sk_C @ X10 @ X9) @ X9))),
% 1.02/1.21      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.02/1.21  thf(t64_zfmisc_1, axiom,
% 1.02/1.21    (![A:$i,B:$i,C:$i]:
% 1.02/1.21     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 1.02/1.21       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 1.02/1.21  thf('2', plain,
% 1.02/1.21      (![X20 : $i, X21 : $i, X23 : $i]:
% 1.02/1.21         ((r2_hidden @ X20 @ (k4_xboole_0 @ X21 @ (k1_tarski @ X23)))
% 1.02/1.21          | ((X20) = (X23))
% 1.02/1.21          | ~ (r2_hidden @ X20 @ X21))),
% 1.02/1.21      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 1.02/1.21  thf('3', plain,
% 1.02/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.21         ((r1_xboole_0 @ X0 @ X1)
% 1.02/1.21          | ((sk_C @ X1 @ X0) = (X2))
% 1.02/1.21          | (r2_hidden @ (sk_C @ X1 @ X0) @ 
% 1.02/1.21             (k4_xboole_0 @ X0 @ (k1_tarski @ X2))))),
% 1.02/1.21      inference('sup-', [status(thm)], ['1', '2'])).
% 1.02/1.21  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.02/1.21  thf('4', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.02/1.21      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.02/1.21  thf(d5_xboole_0, axiom,
% 1.02/1.21    (![A:$i,B:$i,C:$i]:
% 1.02/1.21     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.02/1.21       ( ![D:$i]:
% 1.02/1.21         ( ( r2_hidden @ D @ C ) <=>
% 1.02/1.21           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.02/1.21  thf('5', plain,
% 1.02/1.21      (![X4 : $i, X5 : $i, X8 : $i]:
% 1.02/1.21         (((X8) = (k4_xboole_0 @ X4 @ X5))
% 1.02/1.21          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X4)
% 1.02/1.21          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X8))),
% 1.02/1.21      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.02/1.21  thf('6', plain,
% 1.02/1.21      (![X4 : $i, X5 : $i, X8 : $i]:
% 1.02/1.21         (((X8) = (k4_xboole_0 @ X4 @ X5))
% 1.02/1.21          | ~ (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X5)
% 1.02/1.21          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X8))),
% 1.02/1.21      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.02/1.21  thf('7', plain,
% 1.02/1.21      (![X0 : $i, X1 : $i]:
% 1.02/1.21         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 1.02/1.21          | ((X1) = (k4_xboole_0 @ X0 @ X0))
% 1.02/1.21          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 1.02/1.21          | ((X1) = (k4_xboole_0 @ X0 @ X0)))),
% 1.02/1.21      inference('sup-', [status(thm)], ['5', '6'])).
% 1.02/1.21  thf('8', plain,
% 1.02/1.21      (![X0 : $i, X1 : $i]:
% 1.02/1.21         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 1.02/1.21          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 1.02/1.21      inference('simplify', [status(thm)], ['7'])).
% 1.02/1.21  thf(d1_xboole_0, axiom,
% 1.02/1.21    (![A:$i]:
% 1.02/1.21     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.02/1.21  thf('9', plain,
% 1.02/1.21      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.02/1.21      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.02/1.21  thf('10', plain,
% 1.02/1.21      (![X0 : $i, X1 : $i]:
% 1.02/1.21         (((X0) = (k4_xboole_0 @ X1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 1.02/1.21      inference('sup-', [status(thm)], ['8', '9'])).
% 1.02/1.21  thf('11', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 1.02/1.21      inference('sup-', [status(thm)], ['4', '10'])).
% 1.02/1.21  thf('12', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 1.02/1.21      inference('sup-', [status(thm)], ['4', '10'])).
% 1.02/1.21  thf('13', plain,
% 1.02/1.21      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.02/1.21         (((X20) != (X22))
% 1.02/1.21          | ~ (r2_hidden @ X20 @ (k4_xboole_0 @ X21 @ (k1_tarski @ X22))))),
% 1.02/1.21      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 1.02/1.21  thf('14', plain,
% 1.02/1.21      (![X21 : $i, X22 : $i]:
% 1.02/1.21         ~ (r2_hidden @ X22 @ (k4_xboole_0 @ X21 @ (k1_tarski @ X22)))),
% 1.02/1.21      inference('simplify', [status(thm)], ['13'])).
% 1.02/1.21  thf('15', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.02/1.21      inference('sup-', [status(thm)], ['12', '14'])).
% 1.02/1.21  thf('16', plain,
% 1.02/1.21      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 1.02/1.21      inference('sup-', [status(thm)], ['11', '15'])).
% 1.02/1.21  thf('17', plain,
% 1.02/1.21      (![X0 : $i, X1 : $i]:
% 1.02/1.21         (((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.02/1.21          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 1.02/1.21      inference('sup-', [status(thm)], ['3', '16'])).
% 1.02/1.21  thf('18', plain,
% 1.02/1.21      (![X9 : $i, X10 : $i]:
% 1.02/1.21         ((r1_xboole_0 @ X9 @ X10) | (r2_hidden @ (sk_C @ X10 @ X9) @ X10))),
% 1.02/1.21      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.02/1.21  thf(d3_struct_0, axiom,
% 1.02/1.21    (![A:$i]:
% 1.02/1.21     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.02/1.21  thf('19', plain,
% 1.02/1.21      (![X29 : $i]:
% 1.02/1.21         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 1.02/1.21      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.02/1.21  thf('20', plain,
% 1.02/1.21      ((m1_subset_1 @ sk_B_1 @ 
% 1.02/1.21        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf(d2_yellow_1, axiom,
% 1.02/1.21    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 1.02/1.21  thf('21', plain,
% 1.02/1.21      (![X31 : $i]: ((k3_yellow_1 @ X31) = (k3_lattice3 @ (k1_lattice3 @ X31)))),
% 1.02/1.21      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.02/1.21  thf('22', plain,
% 1.02/1.21      ((m1_subset_1 @ sk_B_1 @ 
% 1.02/1.21        (k1_zfmisc_1 @ 
% 1.02/1.21         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 1.02/1.21      inference('demod', [status(thm)], ['20', '21'])).
% 1.02/1.21  thf('23', plain,
% 1.02/1.21      (((m1_subset_1 @ sk_B_1 @ 
% 1.02/1.21         (k1_zfmisc_1 @ 
% 1.02/1.21          (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))
% 1.02/1.21        | ~ (l1_struct_0 @ sk_A))),
% 1.02/1.21      inference('sup+', [status(thm)], ['19', '22'])).
% 1.02/1.21  thf('24', plain, ((l1_struct_0 @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('25', plain,
% 1.02/1.21      ((m1_subset_1 @ sk_B_1 @ 
% 1.02/1.21        (k1_zfmisc_1 @ 
% 1.02/1.21         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 1.02/1.21      inference('demod', [status(thm)], ['23', '24'])).
% 1.02/1.21  thf(t2_yellow19, axiom,
% 1.02/1.21    (![A:$i]:
% 1.02/1.21     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.02/1.21       ( ![B:$i]:
% 1.02/1.21         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 1.02/1.21             ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 1.02/1.21             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 1.02/1.21             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 1.02/1.21             ( m1_subset_1 @
% 1.02/1.21               B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 1.02/1.21           ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ))).
% 1.02/1.21  thf('26', plain,
% 1.02/1.21      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.02/1.21         ((v1_xboole_0 @ X34)
% 1.02/1.21          | ~ (v1_subset_1 @ X34 @ (u1_struct_0 @ (k3_yellow_1 @ X35)))
% 1.02/1.21          | ~ (v2_waybel_0 @ X34 @ (k3_yellow_1 @ X35))
% 1.02/1.21          | ~ (v13_waybel_0 @ X34 @ (k3_yellow_1 @ X35))
% 1.02/1.21          | ~ (m1_subset_1 @ X34 @ 
% 1.02/1.21               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X35))))
% 1.02/1.21          | ~ (r2_hidden @ X36 @ X34)
% 1.02/1.21          | ~ (v1_xboole_0 @ X36)
% 1.02/1.21          | (v1_xboole_0 @ X35))),
% 1.02/1.21      inference('cnf', [status(esa)], [t2_yellow19])).
% 1.02/1.21  thf('27', plain,
% 1.02/1.21      (![X31 : $i]: ((k3_yellow_1 @ X31) = (k3_lattice3 @ (k1_lattice3 @ X31)))),
% 1.02/1.21      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.02/1.21  thf('28', plain,
% 1.02/1.21      (![X31 : $i]: ((k3_yellow_1 @ X31) = (k3_lattice3 @ (k1_lattice3 @ X31)))),
% 1.02/1.21      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.02/1.21  thf('29', plain,
% 1.02/1.21      (![X31 : $i]: ((k3_yellow_1 @ X31) = (k3_lattice3 @ (k1_lattice3 @ X31)))),
% 1.02/1.21      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.02/1.21  thf('30', plain,
% 1.02/1.21      (![X31 : $i]: ((k3_yellow_1 @ X31) = (k3_lattice3 @ (k1_lattice3 @ X31)))),
% 1.02/1.21      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.02/1.21  thf('31', plain,
% 1.02/1.21      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.02/1.21         ((v1_xboole_0 @ X34)
% 1.02/1.21          | ~ (v1_subset_1 @ X34 @ 
% 1.02/1.21               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X35))))
% 1.02/1.21          | ~ (v2_waybel_0 @ X34 @ (k3_lattice3 @ (k1_lattice3 @ X35)))
% 1.02/1.21          | ~ (v13_waybel_0 @ X34 @ (k3_lattice3 @ (k1_lattice3 @ X35)))
% 1.02/1.21          | ~ (m1_subset_1 @ X34 @ 
% 1.02/1.21               (k1_zfmisc_1 @ 
% 1.02/1.21                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X35)))))
% 1.02/1.21          | ~ (r2_hidden @ X36 @ X34)
% 1.02/1.21          | ~ (v1_xboole_0 @ X36)
% 1.02/1.21          | (v1_xboole_0 @ X35))),
% 1.02/1.21      inference('demod', [status(thm)], ['26', '27', '28', '29', '30'])).
% 1.02/1.21  thf('32', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.02/1.21          | ~ (v1_xboole_0 @ X0)
% 1.02/1.21          | ~ (r2_hidden @ X0 @ sk_B_1)
% 1.02/1.21          | ~ (v13_waybel_0 @ sk_B_1 @ 
% 1.02/1.21               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 1.02/1.21          | ~ (v2_waybel_0 @ sk_B_1 @ 
% 1.02/1.21               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 1.02/1.21          | ~ (v1_subset_1 @ sk_B_1 @ 
% 1.02/1.21               (u1_struct_0 @ 
% 1.02/1.21                (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))
% 1.02/1.21          | (v1_xboole_0 @ sk_B_1))),
% 1.02/1.21      inference('sup-', [status(thm)], ['25', '31'])).
% 1.02/1.21  thf('33', plain,
% 1.02/1.21      (![X29 : $i]:
% 1.02/1.21         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 1.02/1.21      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.02/1.21  thf('34', plain,
% 1.02/1.21      ((v13_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('35', plain,
% 1.02/1.21      (![X31 : $i]: ((k3_yellow_1 @ X31) = (k3_lattice3 @ (k1_lattice3 @ X31)))),
% 1.02/1.21      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.02/1.21  thf('36', plain,
% 1.02/1.21      ((v13_waybel_0 @ sk_B_1 @ 
% 1.02/1.21        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 1.02/1.21      inference('demod', [status(thm)], ['34', '35'])).
% 1.02/1.21  thf('37', plain,
% 1.02/1.21      (((v13_waybel_0 @ sk_B_1 @ 
% 1.02/1.21         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 1.02/1.21        | ~ (l1_struct_0 @ sk_A))),
% 1.02/1.21      inference('sup+', [status(thm)], ['33', '36'])).
% 1.02/1.21  thf('38', plain, ((l1_struct_0 @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('39', plain,
% 1.02/1.21      ((v13_waybel_0 @ sk_B_1 @ 
% 1.02/1.21        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 1.02/1.21      inference('demod', [status(thm)], ['37', '38'])).
% 1.02/1.21  thf('40', plain,
% 1.02/1.21      (![X29 : $i]:
% 1.02/1.21         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 1.02/1.21      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.02/1.21  thf('41', plain,
% 1.02/1.21      ((v2_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('42', plain,
% 1.02/1.21      (![X31 : $i]: ((k3_yellow_1 @ X31) = (k3_lattice3 @ (k1_lattice3 @ X31)))),
% 1.02/1.21      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.02/1.21  thf('43', plain,
% 1.02/1.21      ((v2_waybel_0 @ sk_B_1 @ 
% 1.02/1.21        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 1.02/1.21      inference('demod', [status(thm)], ['41', '42'])).
% 1.02/1.21  thf('44', plain,
% 1.02/1.21      (((v2_waybel_0 @ sk_B_1 @ 
% 1.02/1.21         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 1.02/1.21        | ~ (l1_struct_0 @ sk_A))),
% 1.02/1.21      inference('sup+', [status(thm)], ['40', '43'])).
% 1.02/1.21  thf('45', plain, ((l1_struct_0 @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('46', plain,
% 1.02/1.21      ((v2_waybel_0 @ sk_B_1 @ 
% 1.02/1.21        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 1.02/1.21      inference('demod', [status(thm)], ['44', '45'])).
% 1.02/1.21  thf('47', plain,
% 1.02/1.21      (![X29 : $i]:
% 1.02/1.21         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 1.02/1.21      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.02/1.21  thf('48', plain,
% 1.02/1.21      ((v1_subset_1 @ sk_B_1 @ 
% 1.02/1.21        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('49', plain,
% 1.02/1.21      (![X31 : $i]: ((k3_yellow_1 @ X31) = (k3_lattice3 @ (k1_lattice3 @ X31)))),
% 1.02/1.21      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.02/1.21  thf('50', plain,
% 1.02/1.21      ((v1_subset_1 @ sk_B_1 @ 
% 1.02/1.21        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 1.02/1.21      inference('demod', [status(thm)], ['48', '49'])).
% 1.02/1.21  thf('51', plain,
% 1.02/1.21      (((v1_subset_1 @ sk_B_1 @ 
% 1.02/1.21         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))
% 1.02/1.21        | ~ (l1_struct_0 @ sk_A))),
% 1.02/1.21      inference('sup+', [status(thm)], ['47', '50'])).
% 1.02/1.21  thf('52', plain, ((l1_struct_0 @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('53', plain,
% 1.02/1.21      ((v1_subset_1 @ sk_B_1 @ 
% 1.02/1.21        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 1.02/1.21      inference('demod', [status(thm)], ['51', '52'])).
% 1.02/1.21  thf('54', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.02/1.21          | ~ (v1_xboole_0 @ X0)
% 1.02/1.21          | ~ (r2_hidden @ X0 @ sk_B_1)
% 1.02/1.21          | (v1_xboole_0 @ sk_B_1))),
% 1.02/1.21      inference('demod', [status(thm)], ['32', '39', '46', '53'])).
% 1.02/1.21  thf('55', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         ((r1_xboole_0 @ X0 @ sk_B_1)
% 1.02/1.21          | (v1_xboole_0 @ sk_B_1)
% 1.02/1.21          | ~ (v1_xboole_0 @ (sk_C @ sk_B_1 @ X0))
% 1.02/1.21          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.21      inference('sup-', [status(thm)], ['18', '54'])).
% 1.02/1.21  thf('56', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (~ (v1_xboole_0 @ X0)
% 1.02/1.21          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_1)
% 1.02/1.21          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.02/1.21          | (v1_xboole_0 @ sk_B_1)
% 1.02/1.21          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_1))),
% 1.02/1.21      inference('sup-', [status(thm)], ['17', '55'])).
% 1.02/1.21  thf('57', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         ((v1_xboole_0 @ sk_B_1)
% 1.02/1.21          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.02/1.21          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_1)
% 1.02/1.21          | ~ (v1_xboole_0 @ X0))),
% 1.02/1.21      inference('simplify', [status(thm)], ['56'])).
% 1.02/1.21  thf(fc2_struct_0, axiom,
% 1.02/1.21    (![A:$i]:
% 1.02/1.21     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.02/1.21       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.02/1.21  thf('58', plain,
% 1.02/1.21      (![X30 : $i]:
% 1.02/1.21         (~ (v1_xboole_0 @ (u1_struct_0 @ X30))
% 1.02/1.21          | ~ (l1_struct_0 @ X30)
% 1.02/1.21          | (v2_struct_0 @ X30))),
% 1.02/1.21      inference('cnf', [status(esa)], [fc2_struct_0])).
% 1.02/1.21  thf('59', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (~ (v1_xboole_0 @ X0)
% 1.02/1.21          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_1)
% 1.02/1.21          | (v1_xboole_0 @ sk_B_1)
% 1.02/1.21          | (v2_struct_0 @ sk_A)
% 1.02/1.21          | ~ (l1_struct_0 @ sk_A))),
% 1.02/1.21      inference('sup-', [status(thm)], ['57', '58'])).
% 1.02/1.21  thf('60', plain, ((l1_struct_0 @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('61', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (~ (v1_xboole_0 @ X0)
% 1.02/1.21          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_1)
% 1.02/1.21          | (v1_xboole_0 @ sk_B_1)
% 1.02/1.21          | (v2_struct_0 @ sk_A))),
% 1.02/1.21      inference('demod', [status(thm)], ['59', '60'])).
% 1.02/1.21  thf('62', plain,
% 1.02/1.21      (![X9 : $i, X10 : $i]:
% 1.02/1.21         ((r1_xboole_0 @ X9 @ X10) | (r2_hidden @ (sk_C @ X10 @ X9) @ X9))),
% 1.02/1.21      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.02/1.21  thf('63', plain,
% 1.02/1.21      (![X9 : $i, X10 : $i]:
% 1.02/1.21         ((r1_xboole_0 @ X9 @ X10) | (r2_hidden @ (sk_C @ X10 @ X9) @ X10))),
% 1.02/1.21      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.02/1.21  thf('64', plain,
% 1.02/1.21      (![X9 : $i, X11 : $i, X12 : $i]:
% 1.02/1.21         (~ (r2_hidden @ X11 @ X9)
% 1.02/1.21          | ~ (r2_hidden @ X11 @ X12)
% 1.02/1.21          | ~ (r1_xboole_0 @ X9 @ X12))),
% 1.02/1.21      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.02/1.21  thf('65', plain,
% 1.02/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.21         ((r1_xboole_0 @ X1 @ X0)
% 1.02/1.21          | ~ (r1_xboole_0 @ X0 @ X2)
% 1.02/1.21          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 1.02/1.21      inference('sup-', [status(thm)], ['63', '64'])).
% 1.02/1.21  thf('66', plain,
% 1.02/1.21      (![X0 : $i, X1 : $i]:
% 1.02/1.21         ((r1_xboole_0 @ X0 @ X1)
% 1.02/1.21          | ~ (r1_xboole_0 @ X1 @ X0)
% 1.02/1.21          | (r1_xboole_0 @ X0 @ X1))),
% 1.02/1.21      inference('sup-', [status(thm)], ['62', '65'])).
% 1.02/1.21  thf('67', plain,
% 1.02/1.21      (![X0 : $i, X1 : $i]:
% 1.02/1.21         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 1.02/1.21      inference('simplify', [status(thm)], ['66'])).
% 1.02/1.21  thf('68', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         ((v2_struct_0 @ sk_A)
% 1.02/1.21          | (v1_xboole_0 @ sk_B_1)
% 1.02/1.21          | ~ (v1_xboole_0 @ X0)
% 1.02/1.21          | (r1_xboole_0 @ sk_B_1 @ (k1_tarski @ X0)))),
% 1.02/1.21      inference('sup-', [status(thm)], ['61', '67'])).
% 1.02/1.21  thf(t83_xboole_1, axiom,
% 1.02/1.21    (![A:$i,B:$i]:
% 1.02/1.21     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.02/1.21  thf('69', plain,
% 1.02/1.21      (![X15 : $i, X16 : $i]:
% 1.02/1.21         (((k4_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_xboole_0 @ X15 @ X16))),
% 1.02/1.21      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.02/1.21  thf('70', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (~ (v1_xboole_0 @ X0)
% 1.02/1.21          | (v1_xboole_0 @ sk_B_1)
% 1.02/1.21          | (v2_struct_0 @ sk_A)
% 1.02/1.21          | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ X0)) = (sk_B_1)))),
% 1.02/1.21      inference('sup-', [status(thm)], ['68', '69'])).
% 1.02/1.21  thf('71', plain,
% 1.02/1.21      (((sk_B_1)
% 1.02/1.21         != (k2_yellow19 @ sk_A @ 
% 1.02/1.21             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('72', plain,
% 1.02/1.21      ((m1_subset_1 @ sk_B_1 @ 
% 1.02/1.21        (k1_zfmisc_1 @ 
% 1.02/1.21         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 1.02/1.21      inference('demod', [status(thm)], ['20', '21'])).
% 1.02/1.21  thf(t14_yellow19, axiom,
% 1.02/1.21    (![A:$i]:
% 1.02/1.21     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.02/1.21       ( ![B:$i]:
% 1.02/1.21         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 1.02/1.21             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 1.02/1.21             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 1.02/1.21             ( m1_subset_1 @
% 1.02/1.21               B @ 
% 1.02/1.21               ( k1_zfmisc_1 @
% 1.02/1.21                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 1.02/1.21           ( ( k7_subset_1 @
% 1.02/1.21               ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ 
% 1.02/1.21               ( k1_tarski @ k1_xboole_0 ) ) =
% 1.02/1.21             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 1.02/1.21  thf('73', plain,
% 1.02/1.21      (![X32 : $i, X33 : $i]:
% 1.02/1.21         ((v1_xboole_0 @ X32)
% 1.02/1.21          | ~ (v2_waybel_0 @ X32 @ (k3_yellow_1 @ (k2_struct_0 @ X33)))
% 1.02/1.21          | ~ (v13_waybel_0 @ X32 @ (k3_yellow_1 @ (k2_struct_0 @ X33)))
% 1.02/1.21          | ~ (m1_subset_1 @ X32 @ 
% 1.02/1.21               (k1_zfmisc_1 @ 
% 1.02/1.21                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X33)))))
% 1.02/1.21          | ((k7_subset_1 @ 
% 1.02/1.21              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X33))) @ X32 @ 
% 1.02/1.21              (k1_tarski @ k1_xboole_0))
% 1.02/1.21              = (k2_yellow19 @ X33 @ 
% 1.02/1.21                 (k3_yellow19 @ X33 @ (k2_struct_0 @ X33) @ X32)))
% 1.02/1.21          | ~ (l1_struct_0 @ X33)
% 1.02/1.21          | (v2_struct_0 @ X33))),
% 1.02/1.21      inference('cnf', [status(esa)], [t14_yellow19])).
% 1.02/1.21  thf('74', plain,
% 1.02/1.21      (![X31 : $i]: ((k3_yellow_1 @ X31) = (k3_lattice3 @ (k1_lattice3 @ X31)))),
% 1.02/1.21      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.02/1.21  thf('75', plain,
% 1.02/1.21      (![X31 : $i]: ((k3_yellow_1 @ X31) = (k3_lattice3 @ (k1_lattice3 @ X31)))),
% 1.02/1.21      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.02/1.21  thf('76', plain,
% 1.02/1.21      (![X31 : $i]: ((k3_yellow_1 @ X31) = (k3_lattice3 @ (k1_lattice3 @ X31)))),
% 1.02/1.21      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.02/1.21  thf('77', plain,
% 1.02/1.21      (![X31 : $i]: ((k3_yellow_1 @ X31) = (k3_lattice3 @ (k1_lattice3 @ X31)))),
% 1.02/1.21      inference('cnf', [status(esa)], [d2_yellow_1])).
% 1.02/1.21  thf('78', plain,
% 1.02/1.21      (![X32 : $i, X33 : $i]:
% 1.02/1.21         ((v1_xboole_0 @ X32)
% 1.02/1.21          | ~ (v2_waybel_0 @ X32 @ 
% 1.02/1.21               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X33))))
% 1.02/1.21          | ~ (v13_waybel_0 @ X32 @ 
% 1.02/1.21               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X33))))
% 1.02/1.21          | ~ (m1_subset_1 @ X32 @ 
% 1.02/1.21               (k1_zfmisc_1 @ 
% 1.02/1.21                (u1_struct_0 @ 
% 1.02/1.21                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X33))))))
% 1.02/1.21          | ((k7_subset_1 @ 
% 1.02/1.21              (u1_struct_0 @ 
% 1.02/1.21               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X33)))) @ 
% 1.02/1.21              X32 @ (k1_tarski @ k1_xboole_0))
% 1.02/1.21              = (k2_yellow19 @ X33 @ 
% 1.02/1.21                 (k3_yellow19 @ X33 @ (k2_struct_0 @ X33) @ X32)))
% 1.02/1.21          | ~ (l1_struct_0 @ X33)
% 1.02/1.21          | (v2_struct_0 @ X33))),
% 1.02/1.21      inference('demod', [status(thm)], ['73', '74', '75', '76', '77'])).
% 1.02/1.21  thf('79', plain,
% 1.02/1.21      (((v2_struct_0 @ sk_A)
% 1.02/1.21        | ~ (l1_struct_0 @ sk_A)
% 1.02/1.21        | ((k7_subset_1 @ 
% 1.02/1.21            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 1.02/1.21            sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 1.02/1.21            = (k2_yellow19 @ sk_A @ 
% 1.02/1.21               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 1.02/1.21        | ~ (v13_waybel_0 @ sk_B_1 @ 
% 1.02/1.21             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 1.02/1.21        | ~ (v2_waybel_0 @ sk_B_1 @ 
% 1.02/1.21             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 1.02/1.21        | (v1_xboole_0 @ sk_B_1))),
% 1.02/1.21      inference('sup-', [status(thm)], ['72', '78'])).
% 1.02/1.21  thf('80', plain, ((l1_struct_0 @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('81', plain,
% 1.02/1.21      ((m1_subset_1 @ sk_B_1 @ 
% 1.02/1.21        (k1_zfmisc_1 @ 
% 1.02/1.21         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 1.02/1.21      inference('demod', [status(thm)], ['20', '21'])).
% 1.02/1.21  thf(redefinition_k7_subset_1, axiom,
% 1.02/1.21    (![A:$i,B:$i,C:$i]:
% 1.02/1.21     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.02/1.21       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.02/1.21  thf('82', plain,
% 1.02/1.21      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.02/1.21         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25))
% 1.02/1.21          | ((k7_subset_1 @ X25 @ X24 @ X26) = (k4_xboole_0 @ X24 @ X26)))),
% 1.02/1.21      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.02/1.21  thf('83', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         ((k7_subset_1 @ 
% 1.02/1.21           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))) @ 
% 1.02/1.21           sk_B_1 @ X0) = (k4_xboole_0 @ sk_B_1 @ X0))),
% 1.02/1.21      inference('sup-', [status(thm)], ['81', '82'])).
% 1.02/1.21  thf('84', plain,
% 1.02/1.21      ((v13_waybel_0 @ sk_B_1 @ 
% 1.02/1.21        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 1.02/1.21      inference('demod', [status(thm)], ['34', '35'])).
% 1.02/1.21  thf('85', plain,
% 1.02/1.21      ((v2_waybel_0 @ sk_B_1 @ 
% 1.02/1.21        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 1.02/1.21      inference('demod', [status(thm)], ['41', '42'])).
% 1.02/1.21  thf('86', plain,
% 1.02/1.21      (((v2_struct_0 @ sk_A)
% 1.02/1.21        | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 1.02/1.21            = (k2_yellow19 @ sk_A @ 
% 1.02/1.21               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 1.02/1.21        | (v1_xboole_0 @ sk_B_1))),
% 1.02/1.21      inference('demod', [status(thm)], ['79', '80', '83', '84', '85'])).
% 1.02/1.21  thf('87', plain, (~ (v2_struct_0 @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('88', plain,
% 1.02/1.21      (((v1_xboole_0 @ sk_B_1)
% 1.02/1.21        | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 1.02/1.21            = (k2_yellow19 @ sk_A @ 
% 1.02/1.21               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))),
% 1.02/1.21      inference('clc', [status(thm)], ['86', '87'])).
% 1.02/1.21  thf('89', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('90', plain,
% 1.02/1.21      (((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 1.02/1.21         = (k2_yellow19 @ sk_A @ 
% 1.02/1.21            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 1.02/1.21      inference('clc', [status(thm)], ['88', '89'])).
% 1.02/1.21  thf('91', plain,
% 1.02/1.21      (((sk_B_1) != (k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0)))),
% 1.02/1.21      inference('demod', [status(thm)], ['71', '90'])).
% 1.02/1.21  thf('92', plain,
% 1.02/1.21      ((((sk_B_1) != (sk_B_1))
% 1.02/1.21        | (v2_struct_0 @ sk_A)
% 1.02/1.21        | (v1_xboole_0 @ sk_B_1)
% 1.02/1.21        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.02/1.21      inference('sup-', [status(thm)], ['70', '91'])).
% 1.02/1.21  thf('93', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.02/1.21      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.02/1.21  thf('94', plain,
% 1.02/1.21      ((((sk_B_1) != (sk_B_1)) | (v2_struct_0 @ sk_A) | (v1_xboole_0 @ sk_B_1))),
% 1.02/1.21      inference('demod', [status(thm)], ['92', '93'])).
% 1.02/1.21  thf('95', plain, (((v1_xboole_0 @ sk_B_1) | (v2_struct_0 @ sk_A))),
% 1.02/1.21      inference('simplify', [status(thm)], ['94'])).
% 1.02/1.21  thf('96', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('97', plain, ((v2_struct_0 @ sk_A)),
% 1.02/1.21      inference('clc', [status(thm)], ['95', '96'])).
% 1.02/1.21  thf('98', plain, ($false), inference('demod', [status(thm)], ['0', '97'])).
% 1.02/1.21  
% 1.02/1.21  % SZS output end Refutation
% 1.02/1.21  
% 1.02/1.22  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
