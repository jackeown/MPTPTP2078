%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.48Y8tJmNhK

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:11 EST 2020

% Result     : Theorem 0.92s
% Output     : Refutation 0.92s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 826 expanded)
%              Number of leaves         :   48 ( 285 expanded)
%              Depth                    :   31
%              Number of atoms          : 1724 (8138 expanded)
%              Number of equality atoms :   78 ( 564 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_yellow_0_type,type,(
    v2_yellow_0: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(t15_yellow_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v2_yellow_0 @ ( k2_yellow_1 @ A ) )
       => ( r2_hidden @ ( k3_tarski @ A ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ( ( v2_yellow_0 @ ( k2_yellow_1 @ A ) )
         => ( r2_hidden @ ( k3_tarski @ A ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t15_yellow_1])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X9: $i] :
      ( ( X9
        = ( k3_tarski @ X5 ) )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X5 ) @ ( sk_D @ X9 @ X5 ) )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('2',plain,(
    v2_yellow_0 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(abstractness_v1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_orders_2 @ A )
       => ( A
          = ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X15: $i] :
      ( ~ ( v1_orders_2 @ X15 )
      | ( X15
        = ( g1_orders_2 @ ( u1_struct_0 @ X15 ) @ ( u1_orders_2 @ X15 ) ) )
      | ~ ( l1_orders_2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_orders_2])).

thf(dt_k1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k1_yellow_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k1_yellow_1 @ A ) @ A )
      & ( v8_relat_2 @ ( k1_yellow_1 @ A ) )
      & ( v4_relat_2 @ ( k1_yellow_1 @ A ) )
      & ( v1_relat_2 @ ( k1_yellow_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X34: $i] :
      ( m1_subset_1 @ ( k1_yellow_1 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_1])).

thf(free_g1_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_orders_2 @ A @ B )
            = ( g1_orders_2 @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( ( g1_orders_2 @ X18 @ X19 )
       != ( g1_orders_2 @ X16 @ X17 ) )
      | ( X18 = X16 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( ( g1_orders_2 @ X0 @ ( k1_yellow_1 @ X0 ) )
       != ( g1_orders_2 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k2_yellow_1 @ A )
      = ( g1_orders_2 @ A @ ( k1_yellow_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X29: $i] :
      ( ( k2_yellow_1 @ X29 )
      = ( g1_orders_2 @ X29 @ ( k1_yellow_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d1_yellow_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( ( k2_yellow_1 @ X0 )
       != ( g1_orders_2 @ X1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_yellow_1 @ X1 )
       != X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_orders_2 @ X0 )
      | ( X1
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X1: $i] :
      ( ( X1
        = ( u1_struct_0 @ ( k2_yellow_1 @ X1 ) ) )
      | ~ ( v1_orders_2 @ ( k2_yellow_1 @ X1 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X36: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('12',plain,(
    ! [X35: $i] :
      ( v1_orders_2 @ ( k2_yellow_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('13',plain,(
    ! [X1: $i] :
      ( X1
      = ( u1_struct_0 @ ( k2_yellow_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['10','11','12'])).

thf(d5_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v2_yellow_0 @ A )
      <=> ? [B: $i] :
            ( ( r2_lattice3 @ A @ ( u1_struct_0 @ A ) @ B )
            & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('14',plain,(
    ! [X27: $i] :
      ( ~ ( v2_yellow_0 @ X27 )
      | ( m1_subset_1 @ ( sk_B @ X27 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_orders_2 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d5_yellow_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ X14 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v2_yellow_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ ( k2_yellow_1 @ X0 ) ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( v2_yellow_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X1: $i] :
      ( X1
      = ( u1_struct_0 @ ( k2_yellow_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['10','11','12'])).

thf('19',plain,(
    ! [X36: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ ( k2_yellow_1 @ X0 ) ) @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v2_yellow_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['2','20'])).

thf('22',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    r2_hidden @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X5: $i,X9: $i] :
      ( ( X9
        = ( k3_tarski @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('25',plain,(
    ! [X5: $i,X9: $i] :
      ( ( X9
        = ( k3_tarski @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('26',plain,(
    ! [X5: $i,X9: $i,X10: $i] :
      ( ( X9
        = ( k3_tarski @ X5 ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ X9 @ X5 ) @ X10 )
      | ~ ( r2_hidden @ X10 @ X5 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X9 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_tarski @ X1 ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( X0
        = ( k3_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_tarski @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_tarski @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_tarski @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( X0
        = ( k3_tarski @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( r2_hidden @ ( sk_D @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ sk_A )
    | ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','30'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('32',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ X11 @ X12 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('33',plain,
    ( ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('35',plain,
    ( ( r2_hidden @ ( sk_D @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ sk_A )
    | ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','30'])).

thf('36',plain,(
    v2_yellow_0 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X1: $i] :
      ( X1
      = ( u1_struct_0 @ ( k2_yellow_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['10','11','12'])).

thf('38',plain,(
    ! [X27: $i] :
      ( ~ ( v2_yellow_0 @ X27 )
      | ( r2_lattice3 @ X27 @ ( u1_struct_0 @ X27 ) @ ( sk_B @ X27 ) )
      | ~ ( l1_orders_2 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d5_yellow_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ ( k2_yellow_1 @ X0 ) @ X0 @ ( sk_B @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v2_yellow_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X36: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ ( k2_yellow_1 @ X0 ) @ X0 @ ( sk_B @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( v2_yellow_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    r2_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_A @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X1: $i] :
      ( X1
      = ( u1_struct_0 @ ( k2_yellow_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['10','11','12'])).

thf(d9_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
         => ( ( r2_lattice3 @ A @ B @ C )
          <=> ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ D @ B )
                 => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) )).

thf('44',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ~ ( r2_lattice3 @ X24 @ X25 @ X23 )
      | ~ ( r2_hidden @ X26 @ X25 )
      | ( r1_orders_2 @ X24 @ X26 @ X23 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_orders_2 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_lattice3 @ ( k2_yellow_1 @ X0 ) @ X3 @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X36: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('47',plain,(
    ! [X1: $i] :
      ( X1
      = ( u1_struct_0 @ ( k2_yellow_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['10','11','12'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_lattice3 @ ( k2_yellow_1 @ X0 ) @ X3 @ X1 ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ X0 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','48'])).

thf('50',plain,(
    v2_yellow_0 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X1: $i] :
      ( X1
      = ( u1_struct_0 @ ( k2_yellow_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['10','11','12'])).

thf('52',plain,(
    ! [X27: $i] :
      ( ~ ( v2_yellow_0 @ X27 )
      | ( m1_subset_1 @ ( sk_B @ X27 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_orders_2 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d5_yellow_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_B @ ( k2_yellow_1 @ X0 ) ) @ X0 )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v2_yellow_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X36: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_B @ ( k2_yellow_1 @ X0 ) ) @ X0 )
      | ~ ( v2_yellow_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ X0 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','56'])).

thf('58',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ X11 @ X12 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ X0 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( sk_D @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','59'])).

thf('61',plain,(
    ! [X1: $i] :
      ( X1
      = ( u1_struct_0 @ ( k2_yellow_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['10','11','12'])).

thf(redefinition_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_orders_2 @ A @ B @ C )
      <=> ( r1_orders_2 @ A @ B @ C ) ) ) )).

thf('62',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_orders_2 @ X21 )
      | ~ ( v3_orders_2 @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ( r3_orders_2 @ X21 @ X20 @ X22 )
      | ~ ( r1_orders_2 @ X21 @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X1: $i] :
      ( X1
      = ( u1_struct_0 @ ( k2_yellow_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['10','11','12'])).

thf(fc5_yellow_1,axiom,(
    ! [A: $i] :
      ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v4_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v3_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('65',plain,(
    ! [X38: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('66',plain,(
    ! [X36: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['63','64','65','66'])).

thf('68',plain,
    ( ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( sk_D @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ ( sk_D @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['60','67'])).

thf('69',plain,(
    m1_subset_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ),
    inference('sup-',[status(thm)],['50','55'])).

thf('70',plain,
    ( ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( sk_D @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ ( sk_D @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( sk_D @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','70'])).

thf('72',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( sk_D @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) )
    | ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf(t3_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
             => ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C )
              <=> ( r1_tarski @ B @ C ) ) ) ) ) )).

thf('73',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( u1_struct_0 @ ( k2_yellow_1 @ X43 ) ) )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X43 ) @ X42 @ X44 )
      | ( r1_tarski @ X42 @ X44 )
      | ~ ( m1_subset_1 @ X44 @ ( u1_struct_0 @ ( k2_yellow_1 @ X43 ) ) )
      | ( v1_xboole_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t3_yellow_1])).

thf('74',plain,(
    ! [X1: $i] :
      ( X1
      = ( u1_struct_0 @ ( k2_yellow_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['10','11','12'])).

thf('75',plain,(
    ! [X1: $i] :
      ( X1
      = ( u1_struct_0 @ ( k2_yellow_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['10','11','12'])).

thf('76',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X42 @ X43 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X43 ) @ X42 @ X44 )
      | ( r1_tarski @ X42 @ X44 )
      | ~ ( m1_subset_1 @ X44 @ X43 )
      | ( v1_xboole_0 @ X43 ) ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,
    ( ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A )
    | ( r1_tarski @ ( sk_D @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ ( sk_D @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['72','76'])).

thf('78',plain,(
    m1_subset_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ),
    inference('sup-',[status(thm)],['50','55'])).

thf('79',plain,
    ( ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ ( sk_D @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ ( sk_D @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) )
    | ( r1_tarski @ ( sk_D @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','79'])).

thf('81',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ ( sk_D @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) )
    | ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
        = ( k3_tarski @ sk_A ) )
      | ( v1_xboole_0 @ sk_A )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( r2_hidden @ ( sk_C_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) )
    | ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) )
    | ( r2_hidden @ ( sk_C_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','83'])).

thf('85',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) )
    | ( r2_hidden @ ( sk_C_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,
    ( ( r2_hidden @ ( sk_D @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ sk_A )
    | ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','30'])).

thf('87',plain,(
    ! [X5: $i,X9: $i] :
      ( ( X9
        = ( k3_tarski @ X5 ) )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X5 ) @ ( sk_D @ X9 @ X5 ) )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('88',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( r2_hidden @ X6 @ X7 )
      | ( X7
       != ( k3_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('89',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ ( k3_tarski @ X5 ) )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k3_tarski @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k3_tarski @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['87','89'])).

thf('91',plain,
    ( ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) )
    | ( r2_hidden @ ( sk_C_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ ( k3_tarski @ sk_A ) )
    | ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) )
    | ( r2_hidden @ ( sk_C_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['86','90'])).

thf('92',plain,
    ( ( r2_hidden @ ( sk_C_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) )
    | ( r2_hidden @ ( sk_C_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ ( k3_tarski @ sk_A ) )
    | ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    r2_hidden @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ),
    inference(clc,[status(thm)],['21','22'])).

thf('94',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('95',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ ( k3_tarski @ X5 ) )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_tarski @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) ) @ ( k3_tarski @ sk_A ) )
      | ( r1_tarski @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('98',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('99',plain,
    ( ( r1_tarski @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ ( k3_tarski @ sk_A ) )
    | ( r1_tarski @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    r1_tarski @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ ( k3_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k3_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) )
    | ( r2_hidden @ ( sk_C_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ ( k3_tarski @ sk_A ) ) ),
    inference(clc,[status(thm)],['92','102'])).

thf('104',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ ( sk_D_1 @ X8 @ X5 ) )
      | ( X7
       != ( k3_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('105',plain,(
    ! [X5: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ ( sk_D_1 @ X8 @ X5 ) )
      | ~ ( r2_hidden @ X8 @ ( k3_tarski @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,
    ( ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) )
    | ( r2_hidden @ ( sk_C_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ ( sk_D_1 @ ( sk_C_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['103','105'])).

thf('107',plain,(
    ! [X5: $i,X9: $i,X10: $i] :
      ( ( X9
        = ( k3_tarski @ X5 ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ X9 @ X5 ) @ X10 )
      | ~ ( r2_hidden @ X10 @ X5 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X9 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('108',plain,
    ( ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_C_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ sk_A ) @ sk_A )
    | ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ~ ( r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ ( sk_C_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) )
    | ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,
    ( ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) )
    | ( r2_hidden @ ( sk_C_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ ( k3_tarski @ sk_A ) ) ),
    inference(clc,[status(thm)],['92','102'])).

thf('111',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ ( sk_D_1 @ X8 @ X5 ) @ X5 )
      | ( X7
       != ( k3_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('112',plain,(
    ! [X5: $i,X8: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X8 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k3_tarski @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,
    ( ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['110','112'])).

thf('114',plain,
    ( ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_C_1 @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ) @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['109','113'])).

thf('115',plain,
    ( ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','114'])).

thf('116',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( ( sk_B @ ( k2_yellow_1 @ sk_A ) )
      = ( k3_tarski @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('119',plain,(
    r2_hidden @ ( sk_B @ ( k2_yellow_1 @ sk_A ) ) @ sk_A ),
    inference(clc,[status(thm)],['21','22'])).

thf('120',plain,
    ( ( r2_hidden @ ( k3_tarski @ sk_A ) @ sk_A )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['118','119'])).

thf('121',plain,(
    ~ ( r2_hidden @ ( k3_tarski @ sk_A ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ),
    inference(clc,[status(thm)],['120','121'])).

thf(fc6_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ A ) )
        & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ) )).

thf('123',plain,(
    ! [X41: $i] :
      ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ X41 ) )
      | ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[fc6_yellow_1])).

thf('124',plain,(
    v1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    $false ),
    inference(demod,[status(thm)],['0','124'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.48Y8tJmNhK
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:47:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.92/1.09  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.92/1.09  % Solved by: fo/fo7.sh
% 0.92/1.09  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.92/1.09  % done 430 iterations in 0.635s
% 0.92/1.09  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.92/1.09  % SZS output start Refutation
% 0.92/1.09  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.92/1.09  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.92/1.09  thf(sk_A_type, type, sk_A: $i).
% 0.92/1.09  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.92/1.09  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.92/1.09  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.92/1.09  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.92/1.09  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.92/1.09  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.92/1.09  thf(v8_relat_2_type, type, v8_relat_2: $i > $o).
% 0.92/1.09  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.92/1.09  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.92/1.09  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.92/1.09  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.92/1.09  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.92/1.09  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.92/1.09  thf(v2_yellow_0_type, type, v2_yellow_0: $i > $o).
% 0.92/1.09  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.92/1.09  thf(v4_relat_2_type, type, v4_relat_2: $i > $o).
% 0.92/1.09  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.92/1.09  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.92/1.09  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.92/1.09  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.92/1.09  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.92/1.09  thf(g1_orders_2_type, type, g1_orders_2: $i > $i > $i).
% 0.92/1.09  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.92/1.09  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.92/1.09  thf(sk_B_type, type, sk_B: $i > $i).
% 0.92/1.09  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.92/1.09  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.92/1.09  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.92/1.09  thf(v1_relat_2_type, type, v1_relat_2: $i > $o).
% 0.92/1.09  thf(t15_yellow_1, conjecture,
% 0.92/1.09    (![A:$i]:
% 0.92/1.09     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.92/1.09       ( ( v2_yellow_0 @ ( k2_yellow_1 @ A ) ) =>
% 0.92/1.09         ( r2_hidden @ ( k3_tarski @ A ) @ A ) ) ))).
% 0.92/1.09  thf(zf_stmt_0, negated_conjecture,
% 0.92/1.09    (~( ![A:$i]:
% 0.92/1.09        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.92/1.09          ( ( v2_yellow_0 @ ( k2_yellow_1 @ A ) ) =>
% 0.92/1.09            ( r2_hidden @ ( k3_tarski @ A ) @ A ) ) ) )),
% 0.92/1.09    inference('cnf.neg', [status(esa)], [t15_yellow_1])).
% 0.92/1.09  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.92/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.09  thf(d4_tarski, axiom,
% 0.92/1.09    (![A:$i,B:$i]:
% 0.92/1.09     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 0.92/1.09       ( ![C:$i]:
% 0.92/1.09         ( ( r2_hidden @ C @ B ) <=>
% 0.92/1.09           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 0.92/1.09  thf('1', plain,
% 0.92/1.09      (![X5 : $i, X9 : $i]:
% 0.92/1.09         (((X9) = (k3_tarski @ X5))
% 0.92/1.09          | (r2_hidden @ (sk_C_1 @ X9 @ X5) @ (sk_D @ X9 @ X5))
% 0.92/1.09          | (r2_hidden @ (sk_C_1 @ X9 @ X5) @ X9))),
% 0.92/1.09      inference('cnf', [status(esa)], [d4_tarski])).
% 0.92/1.09  thf('2', plain, ((v2_yellow_0 @ (k2_yellow_1 @ sk_A))),
% 0.92/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.09  thf(abstractness_v1_orders_2, axiom,
% 0.92/1.09    (![A:$i]:
% 0.92/1.09     ( ( l1_orders_2 @ A ) =>
% 0.92/1.09       ( ( v1_orders_2 @ A ) =>
% 0.92/1.09         ( ( A ) = ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ))).
% 0.92/1.09  thf('3', plain,
% 0.92/1.09      (![X15 : $i]:
% 0.92/1.09         (~ (v1_orders_2 @ X15)
% 0.92/1.09          | ((X15) = (g1_orders_2 @ (u1_struct_0 @ X15) @ (u1_orders_2 @ X15)))
% 0.92/1.09          | ~ (l1_orders_2 @ X15))),
% 0.92/1.09      inference('cnf', [status(esa)], [abstractness_v1_orders_2])).
% 0.92/1.09  thf(dt_k1_yellow_1, axiom,
% 0.92/1.09    (![A:$i]:
% 0.92/1.09     ( ( m1_subset_1 @
% 0.92/1.09         ( k1_yellow_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.92/1.09       ( v1_partfun1 @ ( k1_yellow_1 @ A ) @ A ) & 
% 0.92/1.09       ( v8_relat_2 @ ( k1_yellow_1 @ A ) ) & 
% 0.92/1.09       ( v4_relat_2 @ ( k1_yellow_1 @ A ) ) & 
% 0.92/1.09       ( v1_relat_2 @ ( k1_yellow_1 @ A ) ) ))).
% 0.92/1.09  thf('4', plain,
% 0.92/1.09      (![X34 : $i]:
% 0.92/1.09         (m1_subset_1 @ (k1_yellow_1 @ X34) @ 
% 0.92/1.09          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))),
% 0.92/1.09      inference('cnf', [status(esa)], [dt_k1_yellow_1])).
% 0.92/1.09  thf(free_g1_orders_2, axiom,
% 0.92/1.09    (![A:$i,B:$i]:
% 0.92/1.09     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.92/1.09       ( ![C:$i,D:$i]:
% 0.92/1.09         ( ( ( g1_orders_2 @ A @ B ) = ( g1_orders_2 @ C @ D ) ) =>
% 0.92/1.09           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.92/1.09  thf('5', plain,
% 0.92/1.09      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.92/1.09         (((g1_orders_2 @ X18 @ X19) != (g1_orders_2 @ X16 @ X17))
% 0.92/1.09          | ((X18) = (X16))
% 0.92/1.09          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18))))),
% 0.92/1.09      inference('cnf', [status(esa)], [free_g1_orders_2])).
% 0.92/1.09  thf('6', plain,
% 0.92/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.92/1.09         (((X0) = (X1))
% 0.92/1.09          | ((g1_orders_2 @ X0 @ (k1_yellow_1 @ X0)) != (g1_orders_2 @ X1 @ X2)))),
% 0.92/1.09      inference('sup-', [status(thm)], ['4', '5'])).
% 0.92/1.09  thf(d1_yellow_1, axiom,
% 0.92/1.09    (![A:$i]:
% 0.92/1.09     ( ( k2_yellow_1 @ A ) = ( g1_orders_2 @ A @ ( k1_yellow_1 @ A ) ) ))).
% 0.92/1.09  thf('7', plain,
% 0.92/1.09      (![X29 : $i]:
% 0.92/1.09         ((k2_yellow_1 @ X29) = (g1_orders_2 @ X29 @ (k1_yellow_1 @ X29)))),
% 0.92/1.09      inference('cnf', [status(esa)], [d1_yellow_1])).
% 0.92/1.09  thf('8', plain,
% 0.92/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.92/1.09         (((X0) = (X1)) | ((k2_yellow_1 @ X0) != (g1_orders_2 @ X1 @ X2)))),
% 0.92/1.09      inference('demod', [status(thm)], ['6', '7'])).
% 0.92/1.09  thf('9', plain,
% 0.92/1.09      (![X0 : $i, X1 : $i]:
% 0.92/1.09         (((k2_yellow_1 @ X1) != (X0))
% 0.92/1.09          | ~ (l1_orders_2 @ X0)
% 0.92/1.09          | ~ (v1_orders_2 @ X0)
% 0.92/1.09          | ((X1) = (u1_struct_0 @ X0)))),
% 0.92/1.09      inference('sup-', [status(thm)], ['3', '8'])).
% 0.92/1.09  thf('10', plain,
% 0.92/1.09      (![X1 : $i]:
% 0.92/1.09         (((X1) = (u1_struct_0 @ (k2_yellow_1 @ X1)))
% 0.92/1.09          | ~ (v1_orders_2 @ (k2_yellow_1 @ X1))
% 0.92/1.09          | ~ (l1_orders_2 @ (k2_yellow_1 @ X1)))),
% 0.92/1.09      inference('simplify', [status(thm)], ['9'])).
% 0.92/1.09  thf(dt_k2_yellow_1, axiom,
% 0.92/1.09    (![A:$i]:
% 0.92/1.09     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.92/1.09       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.92/1.09  thf('11', plain, (![X36 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X36))),
% 0.92/1.09      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.92/1.09  thf('12', plain, (![X35 : $i]: (v1_orders_2 @ (k2_yellow_1 @ X35))),
% 0.92/1.09      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.92/1.09  thf('13', plain, (![X1 : $i]: ((X1) = (u1_struct_0 @ (k2_yellow_1 @ X1)))),
% 0.92/1.09      inference('simplify_reflect+', [status(thm)], ['10', '11', '12'])).
% 0.92/1.09  thf(d5_yellow_0, axiom,
% 0.92/1.09    (![A:$i]:
% 0.92/1.09     ( ( l1_orders_2 @ A ) =>
% 0.92/1.09       ( ( v2_yellow_0 @ A ) <=>
% 0.92/1.09         ( ?[B:$i]:
% 0.92/1.09           ( ( r2_lattice3 @ A @ ( u1_struct_0 @ A ) @ B ) & 
% 0.92/1.09             ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.92/1.09  thf('14', plain,
% 0.92/1.09      (![X27 : $i]:
% 0.92/1.09         (~ (v2_yellow_0 @ X27)
% 0.92/1.09          | (m1_subset_1 @ (sk_B @ X27) @ (u1_struct_0 @ X27))
% 0.92/1.09          | ~ (l1_orders_2 @ X27))),
% 0.92/1.09      inference('cnf', [status(esa)], [d5_yellow_0])).
% 0.92/1.09  thf(t2_subset, axiom,
% 0.92/1.09    (![A:$i,B:$i]:
% 0.92/1.09     ( ( m1_subset_1 @ A @ B ) =>
% 0.92/1.09       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.92/1.09  thf('15', plain,
% 0.92/1.09      (![X13 : $i, X14 : $i]:
% 0.92/1.09         ((r2_hidden @ X13 @ X14)
% 0.92/1.09          | (v1_xboole_0 @ X14)
% 0.92/1.09          | ~ (m1_subset_1 @ X13 @ X14))),
% 0.92/1.09      inference('cnf', [status(esa)], [t2_subset])).
% 0.92/1.09  thf('16', plain,
% 0.92/1.09      (![X0 : $i]:
% 0.92/1.09         (~ (l1_orders_2 @ X0)
% 0.92/1.09          | ~ (v2_yellow_0 @ X0)
% 0.92/1.09          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.92/1.09          | (r2_hidden @ (sk_B @ X0) @ (u1_struct_0 @ X0)))),
% 0.92/1.09      inference('sup-', [status(thm)], ['14', '15'])).
% 0.92/1.09  thf('17', plain,
% 0.92/1.09      (![X0 : $i]:
% 0.92/1.09         ((r2_hidden @ (sk_B @ (k2_yellow_1 @ X0)) @ X0)
% 0.92/1.09          | (v1_xboole_0 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.92/1.09          | ~ (v2_yellow_0 @ (k2_yellow_1 @ X0))
% 0.92/1.09          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.92/1.09      inference('sup+', [status(thm)], ['13', '16'])).
% 0.92/1.09  thf('18', plain, (![X1 : $i]: ((X1) = (u1_struct_0 @ (k2_yellow_1 @ X1)))),
% 0.92/1.09      inference('simplify_reflect+', [status(thm)], ['10', '11', '12'])).
% 0.92/1.09  thf('19', plain, (![X36 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X36))),
% 0.92/1.09      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.92/1.09  thf('20', plain,
% 0.92/1.09      (![X0 : $i]:
% 0.92/1.09         ((r2_hidden @ (sk_B @ (k2_yellow_1 @ X0)) @ X0)
% 0.92/1.09          | (v1_xboole_0 @ X0)
% 0.92/1.09          | ~ (v2_yellow_0 @ (k2_yellow_1 @ X0)))),
% 0.92/1.09      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.92/1.09  thf('21', plain,
% 0.92/1.09      (((v1_xboole_0 @ sk_A)
% 0.92/1.09        | (r2_hidden @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A))),
% 0.92/1.09      inference('sup-', [status(thm)], ['2', '20'])).
% 0.92/1.09  thf('22', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.92/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf('23', plain, ((r2_hidden @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A)),
% 0.92/1.10      inference('clc', [status(thm)], ['21', '22'])).
% 0.92/1.10  thf('24', plain,
% 0.92/1.10      (![X5 : $i, X9 : $i]:
% 0.92/1.10         (((X9) = (k3_tarski @ X5))
% 0.92/1.10          | (r2_hidden @ (sk_D @ X9 @ X5) @ X5)
% 0.92/1.10          | (r2_hidden @ (sk_C_1 @ X9 @ X5) @ X9))),
% 0.92/1.10      inference('cnf', [status(esa)], [d4_tarski])).
% 0.92/1.10  thf('25', plain,
% 0.92/1.10      (![X5 : $i, X9 : $i]:
% 0.92/1.10         (((X9) = (k3_tarski @ X5))
% 0.92/1.10          | (r2_hidden @ (sk_D @ X9 @ X5) @ X5)
% 0.92/1.10          | (r2_hidden @ (sk_C_1 @ X9 @ X5) @ X9))),
% 0.92/1.10      inference('cnf', [status(esa)], [d4_tarski])).
% 0.92/1.10  thf('26', plain,
% 0.92/1.10      (![X5 : $i, X9 : $i, X10 : $i]:
% 0.92/1.10         (((X9) = (k3_tarski @ X5))
% 0.92/1.10          | ~ (r2_hidden @ (sk_C_1 @ X9 @ X5) @ X10)
% 0.92/1.10          | ~ (r2_hidden @ X10 @ X5)
% 0.92/1.10          | ~ (r2_hidden @ (sk_C_1 @ X9 @ X5) @ X9))),
% 0.92/1.10      inference('cnf', [status(esa)], [d4_tarski])).
% 0.92/1.10  thf('27', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i]:
% 0.92/1.10         ((r2_hidden @ (sk_D @ X0 @ X1) @ X1)
% 0.92/1.10          | ((X0) = (k3_tarski @ X1))
% 0.92/1.10          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X0)
% 0.92/1.10          | ~ (r2_hidden @ X0 @ X1)
% 0.92/1.10          | ((X0) = (k3_tarski @ X1)))),
% 0.92/1.10      inference('sup-', [status(thm)], ['25', '26'])).
% 0.92/1.10  thf('28', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i]:
% 0.92/1.10         (~ (r2_hidden @ X0 @ X1)
% 0.92/1.10          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X0)
% 0.92/1.10          | ((X0) = (k3_tarski @ X1))
% 0.92/1.10          | (r2_hidden @ (sk_D @ X0 @ X1) @ X1))),
% 0.92/1.10      inference('simplify', [status(thm)], ['27'])).
% 0.92/1.10  thf('29', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i]:
% 0.92/1.10         ((r2_hidden @ (sk_D @ X0 @ X1) @ X1)
% 0.92/1.10          | ((X0) = (k3_tarski @ X1))
% 0.92/1.10          | (r2_hidden @ (sk_D @ X0 @ X1) @ X1)
% 0.92/1.10          | ((X0) = (k3_tarski @ X1))
% 0.92/1.10          | ~ (r2_hidden @ X0 @ X1))),
% 0.92/1.10      inference('sup-', [status(thm)], ['24', '28'])).
% 0.92/1.10  thf('30', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i]:
% 0.92/1.10         (~ (r2_hidden @ X0 @ X1)
% 0.92/1.10          | ((X0) = (k3_tarski @ X1))
% 0.92/1.10          | (r2_hidden @ (sk_D @ X0 @ X1) @ X1))),
% 0.92/1.10      inference('simplify', [status(thm)], ['29'])).
% 0.92/1.10  thf('31', plain,
% 0.92/1.10      (((r2_hidden @ (sk_D @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ sk_A)
% 0.92/1.10        | ((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A)))),
% 0.92/1.10      inference('sup-', [status(thm)], ['23', '30'])).
% 0.92/1.10  thf(t1_subset, axiom,
% 0.92/1.10    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.92/1.10  thf('32', plain,
% 0.92/1.10      (![X11 : $i, X12 : $i]:
% 0.92/1.10         ((m1_subset_1 @ X11 @ X12) | ~ (r2_hidden @ X11 @ X12))),
% 0.92/1.10      inference('cnf', [status(esa)], [t1_subset])).
% 0.92/1.10  thf('33', plain,
% 0.92/1.10      ((((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A))
% 0.92/1.10        | (m1_subset_1 @ (sk_D @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ sk_A))),
% 0.92/1.10      inference('sup-', [status(thm)], ['31', '32'])).
% 0.92/1.10  thf('34', plain,
% 0.92/1.10      ((((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A))
% 0.92/1.10        | (m1_subset_1 @ (sk_D @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ sk_A))),
% 0.92/1.10      inference('sup-', [status(thm)], ['31', '32'])).
% 0.92/1.10  thf('35', plain,
% 0.92/1.10      (((r2_hidden @ (sk_D @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ sk_A)
% 0.92/1.10        | ((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A)))),
% 0.92/1.10      inference('sup-', [status(thm)], ['23', '30'])).
% 0.92/1.10  thf('36', plain, ((v2_yellow_0 @ (k2_yellow_1 @ sk_A))),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf('37', plain, (![X1 : $i]: ((X1) = (u1_struct_0 @ (k2_yellow_1 @ X1)))),
% 0.92/1.10      inference('simplify_reflect+', [status(thm)], ['10', '11', '12'])).
% 0.92/1.10  thf('38', plain,
% 0.92/1.10      (![X27 : $i]:
% 0.92/1.10         (~ (v2_yellow_0 @ X27)
% 0.92/1.10          | (r2_lattice3 @ X27 @ (u1_struct_0 @ X27) @ (sk_B @ X27))
% 0.92/1.10          | ~ (l1_orders_2 @ X27))),
% 0.92/1.10      inference('cnf', [status(esa)], [d5_yellow_0])).
% 0.92/1.10  thf('39', plain,
% 0.92/1.10      (![X0 : $i]:
% 0.92/1.10         ((r2_lattice3 @ (k2_yellow_1 @ X0) @ X0 @ (sk_B @ (k2_yellow_1 @ X0)))
% 0.92/1.10          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.92/1.10          | ~ (v2_yellow_0 @ (k2_yellow_1 @ X0)))),
% 0.92/1.10      inference('sup+', [status(thm)], ['37', '38'])).
% 0.92/1.10  thf('40', plain, (![X36 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X36))),
% 0.92/1.10      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.92/1.10  thf('41', plain,
% 0.92/1.10      (![X0 : $i]:
% 0.92/1.10         ((r2_lattice3 @ (k2_yellow_1 @ X0) @ X0 @ (sk_B @ (k2_yellow_1 @ X0)))
% 0.92/1.10          | ~ (v2_yellow_0 @ (k2_yellow_1 @ X0)))),
% 0.92/1.10      inference('demod', [status(thm)], ['39', '40'])).
% 0.92/1.10  thf('42', plain,
% 0.92/1.10      ((r2_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_A @ 
% 0.92/1.10        (sk_B @ (k2_yellow_1 @ sk_A)))),
% 0.92/1.10      inference('sup-', [status(thm)], ['36', '41'])).
% 0.92/1.10  thf('43', plain, (![X1 : $i]: ((X1) = (u1_struct_0 @ (k2_yellow_1 @ X1)))),
% 0.92/1.10      inference('simplify_reflect+', [status(thm)], ['10', '11', '12'])).
% 0.92/1.10  thf(d9_lattice3, axiom,
% 0.92/1.10    (![A:$i]:
% 0.92/1.10     ( ( l1_orders_2 @ A ) =>
% 0.92/1.10       ( ![B:$i,C:$i]:
% 0.92/1.10         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.92/1.10           ( ( r2_lattice3 @ A @ B @ C ) <=>
% 0.92/1.10             ( ![D:$i]:
% 0.92/1.10               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.92/1.10                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ))).
% 0.92/1.10  thf('44', plain,
% 0.92/1.10      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.92/1.10         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 0.92/1.10          | ~ (r2_lattice3 @ X24 @ X25 @ X23)
% 0.92/1.10          | ~ (r2_hidden @ X26 @ X25)
% 0.92/1.10          | (r1_orders_2 @ X24 @ X26 @ X23)
% 0.92/1.10          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X24))
% 0.92/1.10          | ~ (l1_orders_2 @ X24))),
% 0.92/1.10      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.92/1.10  thf('45', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.92/1.10         (~ (m1_subset_1 @ X1 @ X0)
% 0.92/1.10          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.92/1.10          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.92/1.10          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.92/1.10          | ~ (r2_hidden @ X2 @ X3)
% 0.92/1.10          | ~ (r2_lattice3 @ (k2_yellow_1 @ X0) @ X3 @ X1))),
% 0.92/1.10      inference('sup-', [status(thm)], ['43', '44'])).
% 0.92/1.10  thf('46', plain, (![X36 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X36))),
% 0.92/1.10      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.92/1.10  thf('47', plain, (![X1 : $i]: ((X1) = (u1_struct_0 @ (k2_yellow_1 @ X1)))),
% 0.92/1.10      inference('simplify_reflect+', [status(thm)], ['10', '11', '12'])).
% 0.92/1.10  thf('48', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.92/1.10         (~ (m1_subset_1 @ X1 @ X0)
% 0.92/1.10          | ~ (m1_subset_1 @ X2 @ X0)
% 0.92/1.10          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.92/1.10          | ~ (r2_hidden @ X2 @ X3)
% 0.92/1.10          | ~ (r2_lattice3 @ (k2_yellow_1 @ X0) @ X3 @ X1))),
% 0.92/1.10      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.92/1.10  thf('49', plain,
% 0.92/1.10      (![X0 : $i]:
% 0.92/1.10         (~ (r2_hidden @ X0 @ sk_A)
% 0.92/1.10          | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ X0 @ 
% 0.92/1.10             (sk_B @ (k2_yellow_1 @ sk_A)))
% 0.92/1.10          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.92/1.10          | ~ (m1_subset_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A))),
% 0.92/1.10      inference('sup-', [status(thm)], ['42', '48'])).
% 0.92/1.10  thf('50', plain, ((v2_yellow_0 @ (k2_yellow_1 @ sk_A))),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf('51', plain, (![X1 : $i]: ((X1) = (u1_struct_0 @ (k2_yellow_1 @ X1)))),
% 0.92/1.10      inference('simplify_reflect+', [status(thm)], ['10', '11', '12'])).
% 0.92/1.10  thf('52', plain,
% 0.92/1.10      (![X27 : $i]:
% 0.92/1.10         (~ (v2_yellow_0 @ X27)
% 0.92/1.10          | (m1_subset_1 @ (sk_B @ X27) @ (u1_struct_0 @ X27))
% 0.92/1.10          | ~ (l1_orders_2 @ X27))),
% 0.92/1.10      inference('cnf', [status(esa)], [d5_yellow_0])).
% 0.92/1.10  thf('53', plain,
% 0.92/1.10      (![X0 : $i]:
% 0.92/1.10         ((m1_subset_1 @ (sk_B @ (k2_yellow_1 @ X0)) @ X0)
% 0.92/1.10          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.92/1.10          | ~ (v2_yellow_0 @ (k2_yellow_1 @ X0)))),
% 0.92/1.10      inference('sup+', [status(thm)], ['51', '52'])).
% 0.92/1.10  thf('54', plain, (![X36 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X36))),
% 0.92/1.10      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.92/1.10  thf('55', plain,
% 0.92/1.10      (![X0 : $i]:
% 0.92/1.10         ((m1_subset_1 @ (sk_B @ (k2_yellow_1 @ X0)) @ X0)
% 0.92/1.10          | ~ (v2_yellow_0 @ (k2_yellow_1 @ X0)))),
% 0.92/1.10      inference('demod', [status(thm)], ['53', '54'])).
% 0.92/1.10  thf('56', plain, ((m1_subset_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A)),
% 0.92/1.10      inference('sup-', [status(thm)], ['50', '55'])).
% 0.92/1.10  thf('57', plain,
% 0.92/1.10      (![X0 : $i]:
% 0.92/1.10         (~ (r2_hidden @ X0 @ sk_A)
% 0.92/1.10          | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ X0 @ 
% 0.92/1.10             (sk_B @ (k2_yellow_1 @ sk_A)))
% 0.92/1.10          | ~ (m1_subset_1 @ X0 @ sk_A))),
% 0.92/1.10      inference('demod', [status(thm)], ['49', '56'])).
% 0.92/1.10  thf('58', plain,
% 0.92/1.10      (![X11 : $i, X12 : $i]:
% 0.92/1.10         ((m1_subset_1 @ X11 @ X12) | ~ (r2_hidden @ X11 @ X12))),
% 0.92/1.10      inference('cnf', [status(esa)], [t1_subset])).
% 0.92/1.10  thf('59', plain,
% 0.92/1.10      (![X0 : $i]:
% 0.92/1.10         ((r1_orders_2 @ (k2_yellow_1 @ sk_A) @ X0 @ 
% 0.92/1.10           (sk_B @ (k2_yellow_1 @ sk_A)))
% 0.92/1.10          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.92/1.10      inference('clc', [status(thm)], ['57', '58'])).
% 0.92/1.10  thf('60', plain,
% 0.92/1.10      ((((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A))
% 0.92/1.10        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.92/1.10           (sk_D @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ 
% 0.92/1.10           (sk_B @ (k2_yellow_1 @ sk_A))))),
% 0.92/1.10      inference('sup-', [status(thm)], ['35', '59'])).
% 0.92/1.10  thf('61', plain, (![X1 : $i]: ((X1) = (u1_struct_0 @ (k2_yellow_1 @ X1)))),
% 0.92/1.10      inference('simplify_reflect+', [status(thm)], ['10', '11', '12'])).
% 0.92/1.10  thf(redefinition_r3_orders_2, axiom,
% 0.92/1.10    (![A:$i,B:$i,C:$i]:
% 0.92/1.10     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.92/1.10         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.92/1.10         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.92/1.10       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.92/1.10  thf('62', plain,
% 0.92/1.10      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.92/1.10         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.92/1.10          | ~ (l1_orders_2 @ X21)
% 0.92/1.10          | ~ (v3_orders_2 @ X21)
% 0.92/1.10          | (v2_struct_0 @ X21)
% 0.92/1.10          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.92/1.10          | (r3_orders_2 @ X21 @ X20 @ X22)
% 0.92/1.10          | ~ (r1_orders_2 @ X21 @ X20 @ X22))),
% 0.92/1.10      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.92/1.10  thf('63', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.92/1.10         (~ (m1_subset_1 @ X1 @ X0)
% 0.92/1.10          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.92/1.10          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.92/1.10          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.92/1.10          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.92/1.10          | ~ (v3_orders_2 @ (k2_yellow_1 @ X0))
% 0.92/1.10          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.92/1.10      inference('sup-', [status(thm)], ['61', '62'])).
% 0.92/1.10  thf('64', plain, (![X1 : $i]: ((X1) = (u1_struct_0 @ (k2_yellow_1 @ X1)))),
% 0.92/1.10      inference('simplify_reflect+', [status(thm)], ['10', '11', '12'])).
% 0.92/1.10  thf(fc5_yellow_1, axiom,
% 0.92/1.10    (![A:$i]:
% 0.92/1.10     ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.92/1.10       ( v4_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.92/1.10       ( v3_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.92/1.10       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.92/1.10  thf('65', plain, (![X38 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X38))),
% 0.92/1.10      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.92/1.10  thf('66', plain, (![X36 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X36))),
% 0.92/1.10      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.92/1.10  thf('67', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.92/1.10         (~ (m1_subset_1 @ X1 @ X0)
% 0.92/1.10          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.92/1.10          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.92/1.10          | ~ (m1_subset_1 @ X2 @ X0)
% 0.92/1.10          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.92/1.10      inference('demod', [status(thm)], ['63', '64', '65', '66'])).
% 0.92/1.10  thf('68', plain,
% 0.92/1.10      ((((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A))
% 0.92/1.10        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.92/1.10        | ~ (m1_subset_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A)
% 0.92/1.10        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.92/1.10           (sk_D @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ 
% 0.92/1.10           (sk_B @ (k2_yellow_1 @ sk_A)))
% 0.92/1.10        | ~ (m1_subset_1 @ (sk_D @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ sk_A))),
% 0.92/1.10      inference('sup-', [status(thm)], ['60', '67'])).
% 0.92/1.10  thf('69', plain, ((m1_subset_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A)),
% 0.92/1.10      inference('sup-', [status(thm)], ['50', '55'])).
% 0.92/1.10  thf('70', plain,
% 0.92/1.10      ((((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A))
% 0.92/1.10        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.92/1.10        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.92/1.10           (sk_D @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ 
% 0.92/1.10           (sk_B @ (k2_yellow_1 @ sk_A)))
% 0.92/1.10        | ~ (m1_subset_1 @ (sk_D @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ sk_A))),
% 0.92/1.10      inference('demod', [status(thm)], ['68', '69'])).
% 0.92/1.10  thf('71', plain,
% 0.92/1.10      ((((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A))
% 0.92/1.10        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.92/1.10           (sk_D @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ 
% 0.92/1.10           (sk_B @ (k2_yellow_1 @ sk_A)))
% 0.92/1.10        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.92/1.10        | ((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A)))),
% 0.92/1.10      inference('sup-', [status(thm)], ['34', '70'])).
% 0.92/1.10  thf('72', plain,
% 0.92/1.10      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.92/1.10        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.92/1.10           (sk_D @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ 
% 0.92/1.10           (sk_B @ (k2_yellow_1 @ sk_A)))
% 0.92/1.10        | ((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A)))),
% 0.92/1.10      inference('simplify', [status(thm)], ['71'])).
% 0.92/1.10  thf(t3_yellow_1, axiom,
% 0.92/1.10    (![A:$i]:
% 0.92/1.10     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.92/1.10       ( ![B:$i]:
% 0.92/1.10         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.92/1.10           ( ![C:$i]:
% 0.92/1.10             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.92/1.10               ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C ) <=>
% 0.92/1.10                 ( r1_tarski @ B @ C ) ) ) ) ) ) ))).
% 0.92/1.10  thf('73', plain,
% 0.92/1.10      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.92/1.10         (~ (m1_subset_1 @ X42 @ (u1_struct_0 @ (k2_yellow_1 @ X43)))
% 0.92/1.10          | ~ (r3_orders_2 @ (k2_yellow_1 @ X43) @ X42 @ X44)
% 0.92/1.10          | (r1_tarski @ X42 @ X44)
% 0.92/1.10          | ~ (m1_subset_1 @ X44 @ (u1_struct_0 @ (k2_yellow_1 @ X43)))
% 0.92/1.10          | (v1_xboole_0 @ X43))),
% 0.92/1.10      inference('cnf', [status(esa)], [t3_yellow_1])).
% 0.92/1.10  thf('74', plain, (![X1 : $i]: ((X1) = (u1_struct_0 @ (k2_yellow_1 @ X1)))),
% 0.92/1.10      inference('simplify_reflect+', [status(thm)], ['10', '11', '12'])).
% 0.92/1.10  thf('75', plain, (![X1 : $i]: ((X1) = (u1_struct_0 @ (k2_yellow_1 @ X1)))),
% 0.92/1.10      inference('simplify_reflect+', [status(thm)], ['10', '11', '12'])).
% 0.92/1.10  thf('76', plain,
% 0.92/1.10      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.92/1.10         (~ (m1_subset_1 @ X42 @ X43)
% 0.92/1.10          | ~ (r3_orders_2 @ (k2_yellow_1 @ X43) @ X42 @ X44)
% 0.92/1.10          | (r1_tarski @ X42 @ X44)
% 0.92/1.10          | ~ (m1_subset_1 @ X44 @ X43)
% 0.92/1.10          | (v1_xboole_0 @ X43))),
% 0.92/1.10      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.92/1.10  thf('77', plain,
% 0.92/1.10      ((((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A))
% 0.92/1.10        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.92/1.10        | (v1_xboole_0 @ sk_A)
% 0.92/1.10        | ~ (m1_subset_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A)
% 0.92/1.10        | (r1_tarski @ (sk_D @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ 
% 0.92/1.10           (sk_B @ (k2_yellow_1 @ sk_A)))
% 0.92/1.10        | ~ (m1_subset_1 @ (sk_D @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ sk_A))),
% 0.92/1.10      inference('sup-', [status(thm)], ['72', '76'])).
% 0.92/1.10  thf('78', plain, ((m1_subset_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A)),
% 0.92/1.10      inference('sup-', [status(thm)], ['50', '55'])).
% 0.92/1.10  thf('79', plain,
% 0.92/1.10      ((((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A))
% 0.92/1.10        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.92/1.10        | (v1_xboole_0 @ sk_A)
% 0.92/1.10        | (r1_tarski @ (sk_D @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ 
% 0.92/1.10           (sk_B @ (k2_yellow_1 @ sk_A)))
% 0.92/1.10        | ~ (m1_subset_1 @ (sk_D @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ sk_A))),
% 0.92/1.10      inference('demod', [status(thm)], ['77', '78'])).
% 0.92/1.10  thf('80', plain,
% 0.92/1.10      ((((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A))
% 0.92/1.10        | (r1_tarski @ (sk_D @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ 
% 0.92/1.10           (sk_B @ (k2_yellow_1 @ sk_A)))
% 0.92/1.10        | (v1_xboole_0 @ sk_A)
% 0.92/1.10        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.92/1.10        | ((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A)))),
% 0.92/1.10      inference('sup-', [status(thm)], ['33', '79'])).
% 0.92/1.10  thf('81', plain,
% 0.92/1.10      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.92/1.10        | (v1_xboole_0 @ sk_A)
% 0.92/1.10        | (r1_tarski @ (sk_D @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ 
% 0.92/1.10           (sk_B @ (k2_yellow_1 @ sk_A)))
% 0.92/1.10        | ((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A)))),
% 0.92/1.10      inference('simplify', [status(thm)], ['80'])).
% 0.92/1.10  thf(d3_tarski, axiom,
% 0.92/1.10    (![A:$i,B:$i]:
% 0.92/1.10     ( ( r1_tarski @ A @ B ) <=>
% 0.92/1.10       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.92/1.10  thf('82', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.92/1.10         (~ (r2_hidden @ X0 @ X1)
% 0.92/1.10          | (r2_hidden @ X0 @ X2)
% 0.92/1.10          | ~ (r1_tarski @ X1 @ X2))),
% 0.92/1.10      inference('cnf', [status(esa)], [d3_tarski])).
% 0.92/1.10  thf('83', plain,
% 0.92/1.10      (![X0 : $i]:
% 0.92/1.10         (((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A))
% 0.92/1.10          | (v1_xboole_0 @ sk_A)
% 0.92/1.10          | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.92/1.10          | (r2_hidden @ X0 @ (sk_B @ (k2_yellow_1 @ sk_A)))
% 0.92/1.10          | ~ (r2_hidden @ X0 @ (sk_D @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A)))),
% 0.92/1.10      inference('sup-', [status(thm)], ['81', '82'])).
% 0.92/1.10  thf('84', plain,
% 0.92/1.10      (((r2_hidden @ (sk_C_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ 
% 0.92/1.10         (sk_B @ (k2_yellow_1 @ sk_A)))
% 0.92/1.10        | ((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A))
% 0.92/1.10        | (r2_hidden @ (sk_C_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ 
% 0.92/1.10           (sk_B @ (k2_yellow_1 @ sk_A)))
% 0.92/1.10        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.92/1.10        | (v1_xboole_0 @ sk_A)
% 0.92/1.10        | ((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A)))),
% 0.92/1.10      inference('sup-', [status(thm)], ['1', '83'])).
% 0.92/1.10  thf('85', plain,
% 0.92/1.10      (((v1_xboole_0 @ sk_A)
% 0.92/1.10        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.92/1.10        | ((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A))
% 0.92/1.10        | (r2_hidden @ (sk_C_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ 
% 0.92/1.10           (sk_B @ (k2_yellow_1 @ sk_A))))),
% 0.92/1.10      inference('simplify', [status(thm)], ['84'])).
% 0.92/1.10  thf('86', plain,
% 0.92/1.10      (((r2_hidden @ (sk_D @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ sk_A)
% 0.92/1.10        | ((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A)))),
% 0.92/1.10      inference('sup-', [status(thm)], ['23', '30'])).
% 0.92/1.10  thf('87', plain,
% 0.92/1.10      (![X5 : $i, X9 : $i]:
% 0.92/1.10         (((X9) = (k3_tarski @ X5))
% 0.92/1.10          | (r2_hidden @ (sk_C_1 @ X9 @ X5) @ (sk_D @ X9 @ X5))
% 0.92/1.10          | (r2_hidden @ (sk_C_1 @ X9 @ X5) @ X9))),
% 0.92/1.10      inference('cnf', [status(esa)], [d4_tarski])).
% 0.92/1.10  thf('88', plain,
% 0.92/1.10      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.92/1.10         (~ (r2_hidden @ X4 @ X5)
% 0.92/1.10          | ~ (r2_hidden @ X6 @ X4)
% 0.92/1.10          | (r2_hidden @ X6 @ X7)
% 0.92/1.10          | ((X7) != (k3_tarski @ X5)))),
% 0.92/1.10      inference('cnf', [status(esa)], [d4_tarski])).
% 0.92/1.10  thf('89', plain,
% 0.92/1.10      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.92/1.10         ((r2_hidden @ X6 @ (k3_tarski @ X5))
% 0.92/1.10          | ~ (r2_hidden @ X6 @ X4)
% 0.92/1.10          | ~ (r2_hidden @ X4 @ X5))),
% 0.92/1.10      inference('simplify', [status(thm)], ['88'])).
% 0.92/1.10  thf('90', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.92/1.10         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 0.92/1.10          | ((X1) = (k3_tarski @ X0))
% 0.92/1.10          | ~ (r2_hidden @ (sk_D @ X1 @ X0) @ X2)
% 0.92/1.10          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k3_tarski @ X2)))),
% 0.92/1.10      inference('sup-', [status(thm)], ['87', '89'])).
% 0.92/1.10  thf('91', plain,
% 0.92/1.10      ((((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A))
% 0.92/1.10        | (r2_hidden @ (sk_C_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ 
% 0.92/1.10           (k3_tarski @ sk_A))
% 0.92/1.10        | ((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A))
% 0.92/1.10        | (r2_hidden @ (sk_C_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ 
% 0.92/1.10           (sk_B @ (k2_yellow_1 @ sk_A))))),
% 0.92/1.10      inference('sup-', [status(thm)], ['86', '90'])).
% 0.92/1.10  thf('92', plain,
% 0.92/1.10      (((r2_hidden @ (sk_C_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ 
% 0.92/1.10         (sk_B @ (k2_yellow_1 @ sk_A)))
% 0.92/1.10        | (r2_hidden @ (sk_C_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ 
% 0.92/1.10           (k3_tarski @ sk_A))
% 0.92/1.10        | ((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A)))),
% 0.92/1.10      inference('simplify', [status(thm)], ['91'])).
% 0.92/1.10  thf('93', plain, ((r2_hidden @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A)),
% 0.92/1.10      inference('clc', [status(thm)], ['21', '22'])).
% 0.92/1.10  thf('94', plain,
% 0.92/1.10      (![X1 : $i, X3 : $i]:
% 0.92/1.10         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.92/1.10      inference('cnf', [status(esa)], [d3_tarski])).
% 0.92/1.10  thf('95', plain,
% 0.92/1.10      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.92/1.10         ((r2_hidden @ X6 @ (k3_tarski @ X5))
% 0.92/1.10          | ~ (r2_hidden @ X6 @ X4)
% 0.92/1.10          | ~ (r2_hidden @ X4 @ X5))),
% 0.92/1.10      inference('simplify', [status(thm)], ['88'])).
% 0.92/1.10  thf('96', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.92/1.10         ((r1_tarski @ X0 @ X1)
% 0.92/1.10          | ~ (r2_hidden @ X0 @ X2)
% 0.92/1.10          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_tarski @ X2)))),
% 0.92/1.10      inference('sup-', [status(thm)], ['94', '95'])).
% 0.92/1.10  thf('97', plain,
% 0.92/1.10      (![X0 : $i]:
% 0.92/1.10         ((r2_hidden @ (sk_C @ X0 @ (sk_B @ (k2_yellow_1 @ sk_A))) @ 
% 0.92/1.10           (k3_tarski @ sk_A))
% 0.92/1.10          | (r1_tarski @ (sk_B @ (k2_yellow_1 @ sk_A)) @ X0))),
% 0.92/1.10      inference('sup-', [status(thm)], ['93', '96'])).
% 0.92/1.10  thf('98', plain,
% 0.92/1.10      (![X1 : $i, X3 : $i]:
% 0.92/1.10         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.92/1.10      inference('cnf', [status(esa)], [d3_tarski])).
% 0.92/1.10  thf('99', plain,
% 0.92/1.10      (((r1_tarski @ (sk_B @ (k2_yellow_1 @ sk_A)) @ (k3_tarski @ sk_A))
% 0.92/1.10        | (r1_tarski @ (sk_B @ (k2_yellow_1 @ sk_A)) @ (k3_tarski @ sk_A)))),
% 0.92/1.10      inference('sup-', [status(thm)], ['97', '98'])).
% 0.92/1.10  thf('100', plain,
% 0.92/1.10      ((r1_tarski @ (sk_B @ (k2_yellow_1 @ sk_A)) @ (k3_tarski @ sk_A))),
% 0.92/1.10      inference('simplify', [status(thm)], ['99'])).
% 0.92/1.10  thf('101', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.92/1.10         (~ (r2_hidden @ X0 @ X1)
% 0.92/1.10          | (r2_hidden @ X0 @ X2)
% 0.92/1.10          | ~ (r1_tarski @ X1 @ X2))),
% 0.92/1.10      inference('cnf', [status(esa)], [d3_tarski])).
% 0.92/1.10  thf('102', plain,
% 0.92/1.10      (![X0 : $i]:
% 0.92/1.10         ((r2_hidden @ X0 @ (k3_tarski @ sk_A))
% 0.92/1.10          | ~ (r2_hidden @ X0 @ (sk_B @ (k2_yellow_1 @ sk_A))))),
% 0.92/1.10      inference('sup-', [status(thm)], ['100', '101'])).
% 0.92/1.10  thf('103', plain,
% 0.92/1.10      ((((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A))
% 0.92/1.10        | (r2_hidden @ (sk_C_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ 
% 0.92/1.10           (k3_tarski @ sk_A)))),
% 0.92/1.10      inference('clc', [status(thm)], ['92', '102'])).
% 0.92/1.10  thf('104', plain,
% 0.92/1.10      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.92/1.10         (~ (r2_hidden @ X8 @ X7)
% 0.92/1.10          | (r2_hidden @ X8 @ (sk_D_1 @ X8 @ X5))
% 0.92/1.10          | ((X7) != (k3_tarski @ X5)))),
% 0.92/1.10      inference('cnf', [status(esa)], [d4_tarski])).
% 0.92/1.10  thf('105', plain,
% 0.92/1.10      (![X5 : $i, X8 : $i]:
% 0.92/1.10         ((r2_hidden @ X8 @ (sk_D_1 @ X8 @ X5))
% 0.92/1.10          | ~ (r2_hidden @ X8 @ (k3_tarski @ X5)))),
% 0.92/1.10      inference('simplify', [status(thm)], ['104'])).
% 0.92/1.10  thf('106', plain,
% 0.92/1.10      ((((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A))
% 0.92/1.10        | (r2_hidden @ (sk_C_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ 
% 0.92/1.10           (sk_D_1 @ (sk_C_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ sk_A)))),
% 0.92/1.10      inference('sup-', [status(thm)], ['103', '105'])).
% 0.92/1.10  thf('107', plain,
% 0.92/1.10      (![X5 : $i, X9 : $i, X10 : $i]:
% 0.92/1.10         (((X9) = (k3_tarski @ X5))
% 0.92/1.10          | ~ (r2_hidden @ (sk_C_1 @ X9 @ X5) @ X10)
% 0.92/1.10          | ~ (r2_hidden @ X10 @ X5)
% 0.92/1.10          | ~ (r2_hidden @ (sk_C_1 @ X9 @ X5) @ X9))),
% 0.92/1.10      inference('cnf', [status(esa)], [d4_tarski])).
% 0.92/1.10  thf('108', plain,
% 0.92/1.10      ((((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A))
% 0.92/1.10        | ~ (r2_hidden @ (sk_C_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ 
% 0.92/1.10             (sk_B @ (k2_yellow_1 @ sk_A)))
% 0.92/1.10        | ~ (r2_hidden @ 
% 0.92/1.10             (sk_D_1 @ (sk_C_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ sk_A) @ 
% 0.92/1.10             sk_A)
% 0.92/1.10        | ((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A)))),
% 0.92/1.10      inference('sup-', [status(thm)], ['106', '107'])).
% 0.92/1.10  thf('109', plain,
% 0.92/1.10      ((~ (r2_hidden @ 
% 0.92/1.10           (sk_D_1 @ (sk_C_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ sk_A) @ 
% 0.92/1.10           sk_A)
% 0.92/1.10        | ~ (r2_hidden @ (sk_C_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ 
% 0.92/1.10             (sk_B @ (k2_yellow_1 @ sk_A)))
% 0.92/1.10        | ((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A)))),
% 0.92/1.10      inference('simplify', [status(thm)], ['108'])).
% 0.92/1.10  thf('110', plain,
% 0.92/1.10      ((((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A))
% 0.92/1.10        | (r2_hidden @ (sk_C_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ 
% 0.92/1.10           (k3_tarski @ sk_A)))),
% 0.92/1.10      inference('clc', [status(thm)], ['92', '102'])).
% 0.92/1.10  thf('111', plain,
% 0.92/1.10      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.92/1.10         (~ (r2_hidden @ X8 @ X7)
% 0.92/1.10          | (r2_hidden @ (sk_D_1 @ X8 @ X5) @ X5)
% 0.92/1.10          | ((X7) != (k3_tarski @ X5)))),
% 0.92/1.10      inference('cnf', [status(esa)], [d4_tarski])).
% 0.92/1.10  thf('112', plain,
% 0.92/1.10      (![X5 : $i, X8 : $i]:
% 0.92/1.10         ((r2_hidden @ (sk_D_1 @ X8 @ X5) @ X5)
% 0.92/1.10          | ~ (r2_hidden @ X8 @ (k3_tarski @ X5)))),
% 0.92/1.10      inference('simplify', [status(thm)], ['111'])).
% 0.92/1.10  thf('113', plain,
% 0.92/1.10      ((((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A))
% 0.92/1.10        | (r2_hidden @ 
% 0.92/1.10           (sk_D_1 @ (sk_C_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ sk_A) @ 
% 0.92/1.10           sk_A))),
% 0.92/1.10      inference('sup-', [status(thm)], ['110', '112'])).
% 0.92/1.10  thf('114', plain,
% 0.92/1.10      ((((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A))
% 0.92/1.10        | ~ (r2_hidden @ (sk_C_1 @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A) @ 
% 0.92/1.10             (sk_B @ (k2_yellow_1 @ sk_A))))),
% 0.92/1.10      inference('clc', [status(thm)], ['109', '113'])).
% 0.92/1.10  thf('115', plain,
% 0.92/1.10      ((((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A))
% 0.92/1.10        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.92/1.10        | (v1_xboole_0 @ sk_A)
% 0.92/1.10        | ((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A)))),
% 0.92/1.10      inference('sup-', [status(thm)], ['85', '114'])).
% 0.92/1.10  thf('116', plain,
% 0.92/1.10      (((v1_xboole_0 @ sk_A)
% 0.92/1.10        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.92/1.10        | ((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A)))),
% 0.92/1.10      inference('simplify', [status(thm)], ['115'])).
% 0.92/1.10  thf('117', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf('118', plain,
% 0.92/1.10      ((((sk_B @ (k2_yellow_1 @ sk_A)) = (k3_tarski @ sk_A))
% 0.92/1.10        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.92/1.10      inference('clc', [status(thm)], ['116', '117'])).
% 0.92/1.10  thf('119', plain, ((r2_hidden @ (sk_B @ (k2_yellow_1 @ sk_A)) @ sk_A)),
% 0.92/1.10      inference('clc', [status(thm)], ['21', '22'])).
% 0.92/1.10  thf('120', plain,
% 0.92/1.10      (((r2_hidden @ (k3_tarski @ sk_A) @ sk_A)
% 0.92/1.10        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.92/1.10      inference('sup+', [status(thm)], ['118', '119'])).
% 0.92/1.10  thf('121', plain, (~ (r2_hidden @ (k3_tarski @ sk_A) @ sk_A)),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf('122', plain, ((v2_struct_0 @ (k2_yellow_1 @ sk_A))),
% 0.92/1.10      inference('clc', [status(thm)], ['120', '121'])).
% 0.92/1.10  thf(fc6_yellow_1, axiom,
% 0.92/1.10    (![A:$i]:
% 0.92/1.10     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.92/1.10       ( ( ~( v2_struct_0 @ ( k2_yellow_1 @ A ) ) ) & 
% 0.92/1.10         ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ))).
% 0.92/1.10  thf('123', plain,
% 0.92/1.10      (![X41 : $i]:
% 0.92/1.10         (~ (v2_struct_0 @ (k2_yellow_1 @ X41)) | (v1_xboole_0 @ X41))),
% 0.92/1.10      inference('cnf', [status(esa)], [fc6_yellow_1])).
% 0.92/1.10  thf('124', plain, ((v1_xboole_0 @ sk_A)),
% 0.92/1.10      inference('sup-', [status(thm)], ['122', '123'])).
% 0.92/1.10  thf('125', plain, ($false), inference('demod', [status(thm)], ['0', '124'])).
% 0.92/1.10  
% 0.92/1.10  % SZS output end Refutation
% 0.92/1.10  
% 0.92/1.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
