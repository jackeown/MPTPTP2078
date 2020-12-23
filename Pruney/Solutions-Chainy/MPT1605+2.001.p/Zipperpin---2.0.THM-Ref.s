%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2DvBntbhW8

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:09 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  256 ( 610 expanded)
%              Number of leaves         :   50 ( 224 expanded)
%              Depth                    :   34
%              Number of atoms          : 2406 (5351 expanded)
%              Number of equality atoms :   46 ( 207 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t13_yellow_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ k1_xboole_0 @ A )
       => ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ( ( r2_hidden @ k1_xboole_0 @ A )
         => ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t13_yellow_1])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d11_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( k3_yellow_0 @ A )
        = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ) )).

thf('1',plain,(
    ! [X25: $i] :
      ( ( ( k3_yellow_0 @ X25 )
        = ( k1_yellow_0 @ X25 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf(t42_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_yellow_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( r1_yellow_0 @ A @ k1_xboole_0 )
        & ( r2_yellow_0 @ A @ ( u1_struct_0 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X35: $i] :
      ( ( r1_yellow_0 @ X35 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X35 )
      | ~ ( v1_yellow_0 @ X35 )
      | ~ ( v5_orders_2 @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_0])).

thf('3',plain,(
    r2_hidden @ k1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ X7 @ X8 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('5',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) )
        = ( k1_yellow_1 @ A ) )
      & ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) )
        = A ) ) )).

thf('6',plain,(
    ! [X42: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

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

thf('7',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ( r2_hidden @ ( sk_D_1 @ X21 @ X23 @ X22 ) @ X23 )
      | ( r2_lattice3 @ X22 @ X23 @ X21 )
      | ~ ( l1_orders_2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( r2_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ X2 @ ( k2_yellow_1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('9',plain,(
    ! [X37: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( r2_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ X2 @ ( k2_yellow_1 @ X0 ) ) @ X2 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ k1_xboole_0 @ X0 @ ( k2_yellow_1 @ sk_A ) ) @ X0 )
      | ( r2_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X25: $i] :
      ( ( ( k3_yellow_0 @ X25 )
        = ( k1_yellow_0 @ X25 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('15',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X42: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(dt_k3_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('20',plain,(
    ! [X34: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X34 ) @ ( u1_struct_0 @ X34 ) )
      | ~ ( l1_orders_2 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ X0 )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X37: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t3_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
             => ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C )
              <=> ( r1_tarski @ B @ C ) ) ) ) ) )).

thf('24',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( u1_struct_0 @ ( k2_yellow_1 @ X45 ) ) )
      | ~ ( r1_tarski @ X44 @ X46 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X45 ) @ X44 @ X46 )
      | ~ ( m1_subset_1 @ X46 @ ( u1_struct_0 @ ( k2_yellow_1 @ X45 ) ) )
      | ( v1_xboole_0 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t3_yellow_1])).

thf('25',plain,(
    ! [X42: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('26',plain,(
    ! [X42: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('27',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ X45 )
      | ~ ( r1_tarski @ X44 @ X46 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X45 ) @ X44 @ X46 )
      | ~ ( m1_subset_1 @ X46 @ X45 )
      | ( v1_xboole_0 @ X45 ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ X1 )
      | ~ ( r1_tarski @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X42: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(redefinition_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_orders_2 @ A @ B @ C )
      <=> ( r1_orders_2 @ A @ B @ C ) ) ) )).

thf('33',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ( r1_orders_2 @ X12 @ X11 @ X13 )
      | ~ ( r3_orders_2 @ X12 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X42: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(fc5_yellow_1,axiom,(
    ! [A: $i] :
      ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v4_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v3_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('36',plain,(
    ! [X39: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('37',plain,(
    ! [X37: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','35','36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ X0 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('41',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ! [X42: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(fc1_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('44',plain,(
    ! [X9: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 )
      | ~ ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc1_struct_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X37: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('47',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('48',plain,(
    ! [X0: $i] :
      ( l1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['42','49'])).

thf('51',plain,(
    ! [X25: $i] :
      ( ( ( k3_yellow_0 @ X25 )
        = ( k1_yellow_0 @ X25 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf(dt_k1_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('52',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_orders_2 @ X32 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X32 @ X33 ) @ ( u1_struct_0 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('53',plain,(
    ! [X34: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X34 ) @ ( u1_struct_0 @ X34 ) )
      | ~ ( l1_orders_2 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_0])).

thf('54',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ( r3_orders_2 @ X12 @ X11 @ X13 )
      | ~ ( r1_orders_2 @ X12 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ X1 )
      | ( r3_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r3_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ X1 )
      | ~ ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( r3_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r3_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( k3_yellow_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r3_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r3_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( k3_yellow_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ ( k1_yellow_0 @ ( k2_yellow_1 @ X0 ) @ k1_xboole_0 ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','60'])).

thf('62',plain,(
    ! [X37: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('63',plain,(
    ! [X39: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ ( k1_yellow_0 @ ( k2_yellow_1 @ X0 ) @ k1_xboole_0 ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ ( k1_yellow_0 @ ( k2_yellow_1 @ X0 ) @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','35','36','37'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ ( k2_yellow_1 @ X0 ) @ k1_xboole_0 ) @ X0 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ ( k1_yellow_0 @ ( k2_yellow_1 @ X0 ) @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X42: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('70',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_orders_2 @ X32 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X32 @ X33 ) @ ( u1_struct_0 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k1_yellow_0 @ ( k2_yellow_1 @ X0 ) @ X1 ) @ X0 )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X37: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_yellow_0 @ ( k2_yellow_1 @ X0 ) @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ ( k1_yellow_0 @ ( k2_yellow_1 @ X0 ) @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['68','73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ ( k1_yellow_0 @ ( k2_yellow_1 @ X0 ) @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X34: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X34 ) @ ( u1_struct_0 @ X34 ) )
      | ~ ( l1_orders_2 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_0])).

thf(t25_orders_2,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( ( r1_orders_2 @ A @ B @ C )
                  & ( r1_orders_2 @ A @ C @ B ) )
               => ( B = C ) ) ) ) ) )).

thf('79',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( r1_orders_2 @ X15 @ X14 @ X16 )
      | ~ ( r1_orders_2 @ X15 @ X16 @ X14 )
      | ( X14 = X16 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( v5_orders_2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t25_orders_2])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k3_yellow_0 @ X0 )
        = X1 )
      | ~ ( r1_orders_2 @ X0 @ X1 @ ( k3_yellow_0 @ X0 ) )
      | ~ ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ X1 )
      | ~ ( r1_orders_2 @ X0 @ X1 @ ( k3_yellow_0 @ X0 ) )
      | ( ( k3_yellow_0 @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ ( k2_yellow_1 @ X0 ) @ k1_xboole_0 ) @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) )
        = ( k1_yellow_0 @ ( k2_yellow_1 @ X0 ) @ k1_xboole_0 ) )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ ( k1_yellow_0 @ ( k2_yellow_1 @ X0 ) @ k1_xboole_0 ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['77','81'])).

thf('83',plain,(
    ! [X37: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('84',plain,(
    ! [X41: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('85',plain,(
    ! [X42: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_yellow_0 @ ( k2_yellow_1 @ X0 ) @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) )
        = ( k1_yellow_0 @ ( k2_yellow_1 @ X0 ) @ k1_xboole_0 ) )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ ( k1_yellow_0 @ ( k2_yellow_1 @ X0 ) @ k1_xboole_0 ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['82','83','84','85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) )
        = ( k1_yellow_0 @ ( k2_yellow_1 @ X0 ) @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','87'])).

thf('89',plain,(
    ! [X37: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) )
        = ( k1_yellow_0 @ ( k2_yellow_1 @ X0 ) @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['42','49'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) )
        = ( k1_yellow_0 @ ( k2_yellow_1 @ X0 ) @ k1_xboole_0 ) ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf(d9_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
         => ( ( r1_yellow_0 @ A @ B )
           => ( ( C
                = ( k1_yellow_0 @ A @ B ) )
            <=> ( ( r2_lattice3 @ A @ B @ C )
                & ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r2_lattice3 @ A @ B @ D )
                     => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ) )).

thf('93',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( X30
       != ( k1_yellow_0 @ X28 @ X29 ) )
      | ~ ( r2_lattice3 @ X28 @ X29 @ X31 )
      | ( r1_orders_2 @ X28 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X28 ) )
      | ~ ( r1_yellow_0 @ X28 @ X29 )
      | ~ ( l1_orders_2 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('94',plain,(
    ! [X28: $i,X29: $i,X31: $i] :
      ( ~ ( l1_orders_2 @ X28 )
      | ~ ( r1_yellow_0 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ X28 @ X29 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X28 ) )
      | ( r1_orders_2 @ X28 @ ( k1_yellow_0 @ X28 @ X29 ) @ X31 )
      | ~ ( r2_lattice3 @ X28 @ X29 @ X31 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( r2_lattice3 @ ( k2_yellow_1 @ X0 ) @ k1_xboole_0 @ X1 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ ( k1_yellow_0 @ ( k2_yellow_1 @ X0 ) @ k1_xboole_0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( r1_yellow_0 @ ( k2_yellow_1 @ X0 ) @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['92','94'])).

thf('96',plain,(
    ! [X42: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('98',plain,(
    ! [X42: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('99',plain,(
    ! [X37: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r2_lattice3 @ ( k2_yellow_1 @ X0 ) @ k1_xboole_0 @ X1 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ ( k1_yellow_0 @ ( k2_yellow_1 @ X0 ) @ k1_xboole_0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r1_yellow_0 @ ( k2_yellow_1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['95','96','97','98','99'])).

thf('101',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( r1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ sk_A )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 ) @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','100'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('102',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('103',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('104',plain,
    ( ~ ( r1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 ) @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 ) @ k1_xboole_0 )
    | ~ ( r1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v5_orders_2 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v1_yellow_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','106'])).

thf('108',plain,(
    ! [X41: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('109',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('110',plain,(
    ! [X42: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(d8_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
         => ( ( r1_lattice3 @ A @ B @ C )
          <=> ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ D @ B )
                 => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) )).

thf('111',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ( r2_hidden @ ( sk_D @ X17 @ X19 @ X18 ) @ X19 )
      | ( r1_lattice3 @ X18 @ X19 @ X17 )
      | ~ ( l1_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( r1_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X2 @ ( k2_yellow_1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X37: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( r1_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X2 @ ( k2_yellow_1 @ X0 ) ) @ X2 ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ ( k2_yellow_1 @ sk_A ) ) @ X0 )
      | ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['109','114'])).

thf('116',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ X7 @ X8 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ X0 @ ( k2_yellow_1 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ X0 @ ( k2_yellow_1 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('119',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('120',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ X45 )
      | ~ ( r1_tarski @ X44 @ X46 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X45 ) @ X44 @ X46 )
      | ~ ( m1_subset_1 @ X46 @ X45 )
      | ( v1_xboole_0 @ X45 ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('123',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['122','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['121','126'])).

thf('128',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('130',plain,
    ( ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_A @ k1_xboole_0 )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ sk_A @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['118','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','35','36','37'])).

thf('132',plain,
    ( ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_A @ k1_xboole_0 )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ sk_A @ ( k2_yellow_1 @ sk_A ) ) @ sk_A )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ sk_A @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('134',plain,
    ( ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_A @ k1_xboole_0 )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ sk_A @ ( k2_yellow_1 @ sk_A ) ) @ sk_A )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ sk_A @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,
    ( ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_A @ k1_xboole_0 )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ sk_A @ ( k2_yellow_1 @ sk_A ) ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['117','134'])).

thf('136',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ sk_A @ ( k2_yellow_1 @ sk_A ) ) )
    | ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_A @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,(
    ! [X42: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('138',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ~ ( r1_orders_2 @ X18 @ X17 @ ( sk_D @ X17 @ X19 @ X18 ) )
      | ( r1_lattice3 @ X18 @ X19 @ X17 )
      | ~ ( l1_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('139',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( r1_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ ( sk_D @ X1 @ X2 @ ( k2_yellow_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X37: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('141',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( r1_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ ( sk_D @ X1 @ X2 @ ( k2_yellow_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,
    ( ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_A @ k1_xboole_0 )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_A @ k1_xboole_0 )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['136','141'])).

thf('143',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('144',plain,
    ( ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_A @ k1_xboole_0 )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_A @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,(
    ! [X42: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(d4_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_yellow_0 @ A )
      <=> ? [B: $i] :
            ( ( r1_lattice3 @ A @ ( u1_struct_0 @ A ) @ B )
            & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('147',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r1_lattice3 @ X26 @ ( u1_struct_0 @ X26 ) @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ( v1_yellow_0 @ X26 )
      | ~ ( l1_orders_2 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d4_yellow_0])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_lattice3 @ ( k2_yellow_1 @ X0 ) @ X0 @ X1 )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( v1_yellow_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X37: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('150',plain,(
    ! [X42: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_lattice3 @ ( k2_yellow_1 @ X0 ) @ X0 @ X1 )
      | ( v1_yellow_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['148','149','150'])).

thf('152',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ sk_A )
    | ( v1_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['145','151'])).

thf('153',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('154',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_yellow_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X37: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('156',plain,(
    ! [X9: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 )
      | ~ ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc1_struct_0])).

thf('157',plain,(
    ! [X34: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X34 ) @ ( u1_struct_0 @ X34 ) )
      | ~ ( l1_orders_2 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_0])).

thf('158',plain,(
    ! [X34: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X34 ) @ ( u1_struct_0 @ X34 ) )
      | ~ ( l1_orders_2 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_0])).

thf('159',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ( r2_hidden @ ( sk_D @ X17 @ X19 @ X18 ) @ X19 )
      | ( r1_lattice3 @ X18 @ X19 @ X17 )
      | ~ ( l1_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_lattice3 @ X0 @ X1 @ ( k3_yellow_0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ ( k3_yellow_0 @ X0 ) @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k3_yellow_0 @ X0 ) @ X1 @ X0 ) @ X1 )
      | ( r1_lattice3 @ X0 @ X1 @ ( k3_yellow_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['160'])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X1 )
      | ( r1_lattice3 @ X1 @ X0 @ ( k3_yellow_0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r1_lattice3 @ X26 @ ( u1_struct_0 @ X26 ) @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ( v1_yellow_0 @ X26 )
      | ~ ( l1_orders_2 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d4_yellow_0])).

thf('165',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v1_yellow_0 @ X0 )
      | ~ ( m1_subset_1 @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( v1_yellow_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['157','166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( v1_yellow_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v1_yellow_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['156','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( v1_yellow_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['155','169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( l1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( v1_yellow_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['170','171'])).

thf('173',plain,(
    v1_yellow_0 @ ( k2_yellow_1 @ sk_A ) ),
    inference(clc,[status(thm)],['154','172'])).

thf('174',plain,(
    ! [X37: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('175',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['107','108','173','174'])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_yellow_0 @ ( k2_yellow_1 @ X0 ) @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('178',plain,(
    ! [X0: $i] :
      ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( k1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','35','36','37'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ X0 ) @ sk_A )
      | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( k1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ X0 ) )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_yellow_0 @ ( k2_yellow_1 @ X0 ) @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('182',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 @ ( k1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['180','181','182'])).

thf('184',plain,(
    ! [X42: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('185',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( r1_orders_2 @ X15 @ X14 @ X16 )
      | ~ ( r1_orders_2 @ X15 @ X16 @ X14 )
      | ( X14 = X16 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( v5_orders_2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t25_orders_2])).

thf('186',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( X1 = X2 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X41: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('188',plain,(
    ! [X37: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('189',plain,(
    ! [X42: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('190',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( X1 = X2 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) ) ),
    inference(demod,[status(thm)],['186','187','188','189'])).

thf('191',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ X0 ) @ k1_xboole_0 )
      | ( ( k1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ X0 )
        = k1_xboole_0 )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['183','190'])).

thf('192',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('193',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_yellow_0 @ ( k2_yellow_1 @ X0 ) @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('194',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ X0 ) @ k1_xboole_0 )
      | ( ( k1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['191','192','193'])).

thf('195',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( ( k1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['175','194'])).

thf('196',plain,
    ( ( ( k1_yellow_0 @ ( k2_yellow_1 @ sk_A ) @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['195'])).

thf('197',plain,
    ( ( ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) )
      = k1_xboole_0 )
    | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['1','196'])).

thf('198',plain,(
    ! [X37: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('199',plain,
    ( ( ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) )
      = k1_xboole_0 )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['197','198'])).

thf('200',plain,(
    ( k3_yellow_0 @ ( k2_yellow_1 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['199','200'])).

thf('202',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('203',plain,(
    v1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,(
    $false ),
    inference(demod,[status(thm)],['0','203'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2DvBntbhW8
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:34:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.91/1.08  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.91/1.08  % Solved by: fo/fo7.sh
% 0.91/1.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.08  % done 631 iterations in 0.618s
% 0.91/1.08  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.91/1.08  % SZS output start Refutation
% 0.91/1.08  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.91/1.08  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.91/1.08  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.91/1.08  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 0.91/1.08  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.91/1.08  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.91/1.08  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.91/1.08  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.91/1.08  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.91/1.08  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.91/1.08  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.08  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.91/1.08  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.91/1.08  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.91/1.08  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.91/1.08  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.91/1.08  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 0.91/1.08  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.91/1.08  thf(r2_yellow_0_type, type, r2_yellow_0: $i > $i > $o).
% 0.91/1.08  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.91/1.08  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.91/1.08  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.91/1.08  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.91/1.08  thf(v1_yellow_0_type, type, v1_yellow_0: $i > $o).
% 0.91/1.08  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.91/1.08  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.91/1.08  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.91/1.08  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 0.91/1.08  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.91/1.08  thf(t13_yellow_1, conjecture,
% 0.91/1.08    (![A:$i]:
% 0.91/1.08     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.91/1.08       ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.91/1.08         ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) ) ))).
% 0.91/1.08  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.08    (~( ![A:$i]:
% 0.91/1.08        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.91/1.08          ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.91/1.08            ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) ) ) )),
% 0.91/1.08    inference('cnf.neg', [status(esa)], [t13_yellow_1])).
% 0.91/1.08  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.91/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.08  thf(d11_yellow_0, axiom,
% 0.91/1.08    (![A:$i]:
% 0.91/1.08     ( ( l1_orders_2 @ A ) =>
% 0.91/1.08       ( ( k3_yellow_0 @ A ) = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ))).
% 0.91/1.08  thf('1', plain,
% 0.91/1.08      (![X25 : $i]:
% 0.91/1.08         (((k3_yellow_0 @ X25) = (k1_yellow_0 @ X25 @ k1_xboole_0))
% 0.91/1.08          | ~ (l1_orders_2 @ X25))),
% 0.91/1.08      inference('cnf', [status(esa)], [d11_yellow_0])).
% 0.91/1.08  thf(t42_yellow_0, axiom,
% 0.91/1.08    (![A:$i]:
% 0.91/1.08     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.91/1.08         ( v1_yellow_0 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.91/1.08       ( ( r1_yellow_0 @ A @ k1_xboole_0 ) & 
% 0.91/1.08         ( r2_yellow_0 @ A @ ( u1_struct_0 @ A ) ) ) ))).
% 0.91/1.08  thf('2', plain,
% 0.91/1.08      (![X35 : $i]:
% 0.91/1.08         ((r1_yellow_0 @ X35 @ k1_xboole_0)
% 0.91/1.08          | ~ (l1_orders_2 @ X35)
% 0.91/1.08          | ~ (v1_yellow_0 @ X35)
% 0.91/1.08          | ~ (v5_orders_2 @ X35)
% 0.91/1.08          | (v2_struct_0 @ X35))),
% 0.91/1.08      inference('cnf', [status(esa)], [t42_yellow_0])).
% 0.91/1.08  thf('3', plain, ((r2_hidden @ k1_xboole_0 @ sk_A)),
% 0.91/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.08  thf(t1_subset, axiom,
% 0.91/1.08    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.91/1.08  thf('4', plain,
% 0.91/1.08      (![X7 : $i, X8 : $i]: ((m1_subset_1 @ X7 @ X8) | ~ (r2_hidden @ X7 @ X8))),
% 0.91/1.08      inference('cnf', [status(esa)], [t1_subset])).
% 0.91/1.08  thf('5', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.91/1.08      inference('sup-', [status(thm)], ['3', '4'])).
% 0.91/1.08  thf(t1_yellow_1, axiom,
% 0.91/1.08    (![A:$i]:
% 0.91/1.08     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.91/1.08       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.91/1.08  thf('6', plain, (![X42 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X42)) = (X42))),
% 0.91/1.08      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.91/1.08  thf(d9_lattice3, axiom,
% 0.91/1.08    (![A:$i]:
% 0.91/1.08     ( ( l1_orders_2 @ A ) =>
% 0.91/1.08       ( ![B:$i,C:$i]:
% 0.91/1.08         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.91/1.08           ( ( r2_lattice3 @ A @ B @ C ) <=>
% 0.91/1.08             ( ![D:$i]:
% 0.91/1.08               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.91/1.08                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ))).
% 0.91/1.08  thf('7', plain,
% 0.91/1.08      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.91/1.08         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 0.91/1.08          | (r2_hidden @ (sk_D_1 @ X21 @ X23 @ X22) @ X23)
% 0.91/1.08          | (r2_lattice3 @ X22 @ X23 @ X21)
% 0.91/1.08          | ~ (l1_orders_2 @ X22))),
% 0.91/1.08      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.91/1.08  thf('8', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.08         (~ (m1_subset_1 @ X1 @ X0)
% 0.91/1.08          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.91/1.08          | (r2_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.91/1.08          | (r2_hidden @ (sk_D_1 @ X1 @ X2 @ (k2_yellow_1 @ X0)) @ X2))),
% 0.91/1.08      inference('sup-', [status(thm)], ['6', '7'])).
% 0.91/1.08  thf(dt_k2_yellow_1, axiom,
% 0.91/1.08    (![A:$i]:
% 0.91/1.08     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.91/1.08       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.91/1.08  thf('9', plain, (![X37 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X37))),
% 0.91/1.08      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.91/1.08  thf('10', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.08         (~ (m1_subset_1 @ X1 @ X0)
% 0.91/1.08          | (r2_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.91/1.08          | (r2_hidden @ (sk_D_1 @ X1 @ X2 @ (k2_yellow_1 @ X0)) @ X2))),
% 0.91/1.08      inference('demod', [status(thm)], ['8', '9'])).
% 0.91/1.08  thf('11', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         ((r2_hidden @ (sk_D_1 @ k1_xboole_0 @ X0 @ (k2_yellow_1 @ sk_A)) @ X0)
% 0.91/1.08          | (r2_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ k1_xboole_0))),
% 0.91/1.08      inference('sup-', [status(thm)], ['5', '10'])).
% 0.91/1.08  thf(d1_xboole_0, axiom,
% 0.91/1.08    (![A:$i]:
% 0.91/1.08     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.91/1.08  thf('12', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.91/1.08      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.91/1.08  thf('13', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         ((r2_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ k1_xboole_0)
% 0.91/1.08          | ~ (v1_xboole_0 @ X0))),
% 0.91/1.08      inference('sup-', [status(thm)], ['11', '12'])).
% 0.91/1.08  thf('14', plain,
% 0.91/1.08      (![X25 : $i]:
% 0.91/1.08         (((k3_yellow_0 @ X25) = (k1_yellow_0 @ X25 @ k1_xboole_0))
% 0.91/1.08          | ~ (l1_orders_2 @ X25))),
% 0.91/1.08      inference('cnf', [status(esa)], [d11_yellow_0])).
% 0.91/1.08  thf(d3_tarski, axiom,
% 0.91/1.08    (![A:$i,B:$i]:
% 0.91/1.08     ( ( r1_tarski @ A @ B ) <=>
% 0.91/1.08       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.91/1.08  thf('15', plain,
% 0.91/1.08      (![X4 : $i, X6 : $i]:
% 0.91/1.08         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.91/1.08      inference('cnf', [status(esa)], [d3_tarski])).
% 0.91/1.08  thf('16', plain,
% 0.91/1.08      (![X4 : $i, X6 : $i]:
% 0.91/1.08         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.91/1.08      inference('cnf', [status(esa)], [d3_tarski])).
% 0.91/1.08  thf('17', plain,
% 0.91/1.08      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.91/1.08      inference('sup-', [status(thm)], ['15', '16'])).
% 0.91/1.08  thf('18', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.91/1.08      inference('simplify', [status(thm)], ['17'])).
% 0.91/1.08  thf('19', plain,
% 0.91/1.08      (![X42 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X42)) = (X42))),
% 0.91/1.08      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.91/1.08  thf(dt_k3_yellow_0, axiom,
% 0.91/1.08    (![A:$i]:
% 0.91/1.08     ( ( l1_orders_2 @ A ) =>
% 0.91/1.08       ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 0.91/1.08  thf('20', plain,
% 0.91/1.08      (![X34 : $i]:
% 0.91/1.08         ((m1_subset_1 @ (k3_yellow_0 @ X34) @ (u1_struct_0 @ X34))
% 0.91/1.08          | ~ (l1_orders_2 @ X34))),
% 0.91/1.08      inference('cnf', [status(esa)], [dt_k3_yellow_0])).
% 0.91/1.08  thf('21', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         ((m1_subset_1 @ (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ X0)
% 0.91/1.08          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.91/1.08      inference('sup+', [status(thm)], ['19', '20'])).
% 0.91/1.08  thf('22', plain, (![X37 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X37))),
% 0.91/1.08      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.91/1.08  thf('23', plain,
% 0.91/1.08      (![X0 : $i]: (m1_subset_1 @ (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ X0)),
% 0.91/1.08      inference('demod', [status(thm)], ['21', '22'])).
% 0.91/1.08  thf(t3_yellow_1, axiom,
% 0.91/1.08    (![A:$i]:
% 0.91/1.08     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.91/1.08       ( ![B:$i]:
% 0.91/1.08         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.91/1.08           ( ![C:$i]:
% 0.91/1.08             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.91/1.08               ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C ) <=>
% 0.91/1.08                 ( r1_tarski @ B @ C ) ) ) ) ) ) ))).
% 0.91/1.08  thf('24', plain,
% 0.91/1.08      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.91/1.08         (~ (m1_subset_1 @ X44 @ (u1_struct_0 @ (k2_yellow_1 @ X45)))
% 0.91/1.08          | ~ (r1_tarski @ X44 @ X46)
% 0.91/1.08          | (r3_orders_2 @ (k2_yellow_1 @ X45) @ X44 @ X46)
% 0.91/1.08          | ~ (m1_subset_1 @ X46 @ (u1_struct_0 @ (k2_yellow_1 @ X45)))
% 0.91/1.08          | (v1_xboole_0 @ X45))),
% 0.91/1.08      inference('cnf', [status(esa)], [t3_yellow_1])).
% 0.91/1.08  thf('25', plain,
% 0.91/1.08      (![X42 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X42)) = (X42))),
% 0.91/1.08      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.91/1.08  thf('26', plain,
% 0.91/1.08      (![X42 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X42)) = (X42))),
% 0.91/1.08      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.91/1.08  thf('27', plain,
% 0.91/1.08      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.91/1.08         (~ (m1_subset_1 @ X44 @ X45)
% 0.91/1.08          | ~ (r1_tarski @ X44 @ X46)
% 0.91/1.08          | (r3_orders_2 @ (k2_yellow_1 @ X45) @ X44 @ X46)
% 0.91/1.08          | ~ (m1_subset_1 @ X46 @ X45)
% 0.91/1.08          | (v1_xboole_0 @ X45))),
% 0.91/1.08      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.91/1.08  thf('28', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         ((v1_xboole_0 @ X0)
% 0.91/1.08          | ~ (m1_subset_1 @ X1 @ X0)
% 0.91/1.08          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ 
% 0.91/1.08             (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ X1)
% 0.91/1.08          | ~ (r1_tarski @ (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ X1))),
% 0.91/1.08      inference('sup-', [status(thm)], ['23', '27'])).
% 0.91/1.08  thf('29', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         ((r3_orders_2 @ (k2_yellow_1 @ X0) @ 
% 0.91/1.08           (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ 
% 0.91/1.08           (k3_yellow_0 @ (k2_yellow_1 @ X0)))
% 0.91/1.08          | ~ (m1_subset_1 @ (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ X0)
% 0.91/1.08          | (v1_xboole_0 @ X0))),
% 0.91/1.08      inference('sup-', [status(thm)], ['18', '28'])).
% 0.91/1.08  thf('30', plain,
% 0.91/1.08      (![X0 : $i]: (m1_subset_1 @ (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ X0)),
% 0.91/1.08      inference('demod', [status(thm)], ['21', '22'])).
% 0.91/1.08  thf('31', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         ((r3_orders_2 @ (k2_yellow_1 @ X0) @ 
% 0.91/1.08           (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ 
% 0.91/1.08           (k3_yellow_0 @ (k2_yellow_1 @ X0)))
% 0.91/1.08          | (v1_xboole_0 @ X0))),
% 0.91/1.08      inference('demod', [status(thm)], ['29', '30'])).
% 0.91/1.08  thf('32', plain,
% 0.91/1.08      (![X42 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X42)) = (X42))),
% 0.91/1.08      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.91/1.08  thf(redefinition_r3_orders_2, axiom,
% 0.91/1.08    (![A:$i,B:$i,C:$i]:
% 0.91/1.08     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.91/1.08         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.91/1.08         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.08       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.91/1.08  thf('33', plain,
% 0.91/1.08      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.91/1.08         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 0.91/1.08          | ~ (l1_orders_2 @ X12)
% 0.91/1.08          | ~ (v3_orders_2 @ X12)
% 0.91/1.08          | (v2_struct_0 @ X12)
% 0.91/1.08          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.91/1.08          | (r1_orders_2 @ X12 @ X11 @ X13)
% 0.91/1.08          | ~ (r3_orders_2 @ X12 @ X11 @ X13))),
% 0.91/1.08      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.91/1.08  thf('34', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.08         (~ (m1_subset_1 @ X1 @ X0)
% 0.91/1.08          | ~ (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.91/1.08          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.91/1.08          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.91/1.08          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.91/1.08          | ~ (v3_orders_2 @ (k2_yellow_1 @ X0))
% 0.91/1.08          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.91/1.08      inference('sup-', [status(thm)], ['32', '33'])).
% 0.91/1.08  thf('35', plain,
% 0.91/1.08      (![X42 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X42)) = (X42))),
% 0.91/1.08      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.91/1.08  thf(fc5_yellow_1, axiom,
% 0.91/1.08    (![A:$i]:
% 0.91/1.08     ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.91/1.08       ( v4_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.91/1.08       ( v3_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.91/1.08       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.91/1.08  thf('36', plain, (![X39 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X39))),
% 0.91/1.08      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.91/1.08  thf('37', plain, (![X37 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X37))),
% 0.91/1.08      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.91/1.08  thf('38', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.08         (~ (m1_subset_1 @ X1 @ X0)
% 0.91/1.08          | ~ (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.91/1.08          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.91/1.08          | ~ (m1_subset_1 @ X2 @ X0)
% 0.91/1.08          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.91/1.08      inference('demod', [status(thm)], ['34', '35', '36', '37'])).
% 0.91/1.08  thf('39', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         ((v1_xboole_0 @ X0)
% 0.91/1.08          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.91/1.08          | ~ (m1_subset_1 @ (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ X0)
% 0.91/1.08          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ 
% 0.91/1.08             (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ 
% 0.91/1.08             (k3_yellow_0 @ (k2_yellow_1 @ X0)))
% 0.91/1.08          | ~ (m1_subset_1 @ (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ X0))),
% 0.91/1.08      inference('sup-', [status(thm)], ['31', '38'])).
% 0.91/1.08  thf('40', plain,
% 0.91/1.08      (![X0 : $i]: (m1_subset_1 @ (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ X0)),
% 0.91/1.08      inference('demod', [status(thm)], ['21', '22'])).
% 0.91/1.08  thf('41', plain,
% 0.91/1.08      (![X0 : $i]: (m1_subset_1 @ (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ X0)),
% 0.91/1.08      inference('demod', [status(thm)], ['21', '22'])).
% 0.91/1.08  thf('42', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         ((v1_xboole_0 @ X0)
% 0.91/1.08          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.91/1.08          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ 
% 0.91/1.08             (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ 
% 0.91/1.08             (k3_yellow_0 @ (k2_yellow_1 @ X0))))),
% 0.91/1.08      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.91/1.08  thf('43', plain,
% 0.91/1.08      (![X42 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X42)) = (X42))),
% 0.91/1.08      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.91/1.08  thf(fc1_struct_0, axiom,
% 0.91/1.08    (![A:$i]:
% 0.91/1.08     ( ( ( v2_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.91/1.08       ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ))).
% 0.91/1.08  thf('44', plain,
% 0.91/1.08      (![X9 : $i]:
% 0.91/1.08         ((v1_xboole_0 @ (u1_struct_0 @ X9))
% 0.91/1.08          | ~ (l1_struct_0 @ X9)
% 0.91/1.08          | ~ (v2_struct_0 @ X9))),
% 0.91/1.08      inference('cnf', [status(esa)], [fc1_struct_0])).
% 0.91/1.08  thf('45', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         ((v1_xboole_0 @ X0)
% 0.91/1.08          | ~ (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.91/1.08          | ~ (l1_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.91/1.08      inference('sup+', [status(thm)], ['43', '44'])).
% 0.91/1.08  thf('46', plain, (![X37 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X37))),
% 0.91/1.08      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.91/1.08  thf(dt_l1_orders_2, axiom,
% 0.91/1.08    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.91/1.08  thf('47', plain,
% 0.91/1.08      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_orders_2 @ X10))),
% 0.91/1.08      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.91/1.08  thf('48', plain, (![X0 : $i]: (l1_struct_0 @ (k2_yellow_1 @ X0))),
% 0.91/1.08      inference('sup-', [status(thm)], ['46', '47'])).
% 0.91/1.08  thf('49', plain,
% 0.91/1.08      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.91/1.08      inference('demod', [status(thm)], ['45', '48'])).
% 0.91/1.08  thf('50', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         ((r1_orders_2 @ (k2_yellow_1 @ X0) @ 
% 0.91/1.08           (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ 
% 0.91/1.08           (k3_yellow_0 @ (k2_yellow_1 @ X0)))
% 0.91/1.08          | (v1_xboole_0 @ X0))),
% 0.91/1.08      inference('clc', [status(thm)], ['42', '49'])).
% 0.91/1.08  thf('51', plain,
% 0.91/1.08      (![X25 : $i]:
% 0.91/1.08         (((k3_yellow_0 @ X25) = (k1_yellow_0 @ X25 @ k1_xboole_0))
% 0.91/1.08          | ~ (l1_orders_2 @ X25))),
% 0.91/1.08      inference('cnf', [status(esa)], [d11_yellow_0])).
% 0.91/1.08  thf(dt_k1_yellow_0, axiom,
% 0.91/1.08    (![A:$i,B:$i]:
% 0.91/1.08     ( ( l1_orders_2 @ A ) =>
% 0.91/1.08       ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.91/1.08  thf('52', plain,
% 0.91/1.08      (![X32 : $i, X33 : $i]:
% 0.91/1.08         (~ (l1_orders_2 @ X32)
% 0.91/1.08          | (m1_subset_1 @ (k1_yellow_0 @ X32 @ X33) @ (u1_struct_0 @ X32)))),
% 0.91/1.08      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.91/1.08  thf('53', plain,
% 0.91/1.08      (![X34 : $i]:
% 0.91/1.08         ((m1_subset_1 @ (k3_yellow_0 @ X34) @ (u1_struct_0 @ X34))
% 0.91/1.08          | ~ (l1_orders_2 @ X34))),
% 0.91/1.08      inference('cnf', [status(esa)], [dt_k3_yellow_0])).
% 0.91/1.08  thf('54', plain,
% 0.91/1.08      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.91/1.08         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 0.91/1.08          | ~ (l1_orders_2 @ X12)
% 0.91/1.08          | ~ (v3_orders_2 @ X12)
% 0.91/1.08          | (v2_struct_0 @ X12)
% 0.91/1.08          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.91/1.08          | (r3_orders_2 @ X12 @ X11 @ X13)
% 0.91/1.08          | ~ (r1_orders_2 @ X12 @ X11 @ X13))),
% 0.91/1.08      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.91/1.08  thf('55', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         (~ (l1_orders_2 @ X0)
% 0.91/1.08          | ~ (r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ X1)
% 0.91/1.08          | (r3_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ X1)
% 0.91/1.08          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.91/1.08          | (v2_struct_0 @ X0)
% 0.91/1.08          | ~ (v3_orders_2 @ X0)
% 0.91/1.08          | ~ (l1_orders_2 @ X0))),
% 0.91/1.08      inference('sup-', [status(thm)], ['53', '54'])).
% 0.91/1.08  thf('56', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         (~ (v3_orders_2 @ X0)
% 0.91/1.08          | (v2_struct_0 @ X0)
% 0.91/1.08          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.91/1.08          | (r3_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ X1)
% 0.91/1.08          | ~ (r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ X1)
% 0.91/1.08          | ~ (l1_orders_2 @ X0))),
% 0.91/1.08      inference('simplify', [status(thm)], ['55'])).
% 0.91/1.08  thf('57', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         (~ (l1_orders_2 @ X0)
% 0.91/1.08          | ~ (l1_orders_2 @ X0)
% 0.91/1.08          | ~ (r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ (k1_yellow_0 @ X0 @ X1))
% 0.91/1.08          | (r3_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ (k1_yellow_0 @ X0 @ X1))
% 0.91/1.08          | (v2_struct_0 @ X0)
% 0.91/1.08          | ~ (v3_orders_2 @ X0))),
% 0.91/1.08      inference('sup-', [status(thm)], ['52', '56'])).
% 0.91/1.08  thf('58', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         (~ (v3_orders_2 @ X0)
% 0.91/1.08          | (v2_struct_0 @ X0)
% 0.91/1.08          | (r3_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ (k1_yellow_0 @ X0 @ X1))
% 0.91/1.08          | ~ (r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ (k1_yellow_0 @ X0 @ X1))
% 0.91/1.08          | ~ (l1_orders_2 @ X0))),
% 0.91/1.08      inference('simplify', [status(thm)], ['57'])).
% 0.91/1.08  thf('59', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         (~ (r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ (k3_yellow_0 @ X0))
% 0.91/1.08          | ~ (l1_orders_2 @ X0)
% 0.91/1.08          | ~ (l1_orders_2 @ X0)
% 0.91/1.08          | (r3_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ 
% 0.91/1.08             (k1_yellow_0 @ X0 @ k1_xboole_0))
% 0.91/1.08          | (v2_struct_0 @ X0)
% 0.91/1.08          | ~ (v3_orders_2 @ X0))),
% 0.91/1.08      inference('sup-', [status(thm)], ['51', '58'])).
% 0.91/1.08  thf('60', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         (~ (v3_orders_2 @ X0)
% 0.91/1.08          | (v2_struct_0 @ X0)
% 0.91/1.08          | (r3_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ 
% 0.91/1.08             (k1_yellow_0 @ X0 @ k1_xboole_0))
% 0.91/1.08          | ~ (l1_orders_2 @ X0)
% 0.91/1.08          | ~ (r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ (k3_yellow_0 @ X0)))),
% 0.91/1.08      inference('simplify', [status(thm)], ['59'])).
% 0.91/1.08  thf('61', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         ((v1_xboole_0 @ X0)
% 0.91/1.08          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.91/1.08          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ 
% 0.91/1.08             (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ 
% 0.91/1.08             (k1_yellow_0 @ (k2_yellow_1 @ X0) @ k1_xboole_0))
% 0.91/1.08          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.91/1.08          | ~ (v3_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.91/1.08      inference('sup-', [status(thm)], ['50', '60'])).
% 0.91/1.08  thf('62', plain, (![X37 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X37))),
% 0.91/1.08      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.91/1.08  thf('63', plain, (![X39 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X39))),
% 0.91/1.08      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.91/1.08  thf('64', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         ((v1_xboole_0 @ X0)
% 0.91/1.08          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ 
% 0.91/1.08             (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ 
% 0.91/1.08             (k1_yellow_0 @ (k2_yellow_1 @ X0) @ k1_xboole_0))
% 0.91/1.08          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.91/1.08      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.91/1.08  thf('65', plain,
% 0.91/1.08      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.91/1.08      inference('demod', [status(thm)], ['45', '48'])).
% 0.91/1.08  thf('66', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         ((r3_orders_2 @ (k2_yellow_1 @ X0) @ 
% 0.91/1.08           (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ 
% 0.91/1.08           (k1_yellow_0 @ (k2_yellow_1 @ X0) @ k1_xboole_0))
% 0.91/1.08          | (v1_xboole_0 @ X0))),
% 0.91/1.08      inference('clc', [status(thm)], ['64', '65'])).
% 0.91/1.08  thf('67', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.08         (~ (m1_subset_1 @ X1 @ X0)
% 0.91/1.08          | ~ (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.91/1.08          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.91/1.08          | ~ (m1_subset_1 @ X2 @ X0)
% 0.91/1.08          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.91/1.08      inference('demod', [status(thm)], ['34', '35', '36', '37'])).
% 0.91/1.08  thf('68', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         ((v1_xboole_0 @ X0)
% 0.91/1.08          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.91/1.08          | ~ (m1_subset_1 @ 
% 0.91/1.08               (k1_yellow_0 @ (k2_yellow_1 @ X0) @ k1_xboole_0) @ X0)
% 0.91/1.08          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ 
% 0.91/1.08             (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ 
% 0.91/1.08             (k1_yellow_0 @ (k2_yellow_1 @ X0) @ k1_xboole_0))
% 0.91/1.08          | ~ (m1_subset_1 @ (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ X0))),
% 0.91/1.08      inference('sup-', [status(thm)], ['66', '67'])).
% 0.91/1.08  thf('69', plain,
% 0.91/1.08      (![X42 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X42)) = (X42))),
% 0.91/1.08      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.91/1.08  thf('70', plain,
% 0.91/1.08      (![X32 : $i, X33 : $i]:
% 0.91/1.08         (~ (l1_orders_2 @ X32)
% 0.91/1.08          | (m1_subset_1 @ (k1_yellow_0 @ X32 @ X33) @ (u1_struct_0 @ X32)))),
% 0.91/1.08      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.91/1.08  thf('71', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         ((m1_subset_1 @ (k1_yellow_0 @ (k2_yellow_1 @ X0) @ X1) @ X0)
% 0.91/1.08          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.91/1.08      inference('sup+', [status(thm)], ['69', '70'])).
% 0.91/1.08  thf('72', plain, (![X37 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X37))),
% 0.91/1.08      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.91/1.08  thf('73', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         (m1_subset_1 @ (k1_yellow_0 @ (k2_yellow_1 @ X0) @ X1) @ X0)),
% 0.91/1.08      inference('demod', [status(thm)], ['71', '72'])).
% 0.91/1.08  thf('74', plain,
% 0.91/1.08      (![X0 : $i]: (m1_subset_1 @ (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ X0)),
% 0.91/1.08      inference('demod', [status(thm)], ['21', '22'])).
% 0.91/1.08  thf('75', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         ((v1_xboole_0 @ X0)
% 0.91/1.08          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.91/1.08          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ 
% 0.91/1.08             (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ 
% 0.91/1.08             (k1_yellow_0 @ (k2_yellow_1 @ X0) @ k1_xboole_0)))),
% 0.91/1.08      inference('demod', [status(thm)], ['68', '73', '74'])).
% 0.91/1.08  thf('76', plain,
% 0.91/1.08      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.91/1.08      inference('demod', [status(thm)], ['45', '48'])).
% 0.91/1.08  thf('77', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         ((r1_orders_2 @ (k2_yellow_1 @ X0) @ 
% 0.91/1.08           (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ 
% 0.91/1.08           (k1_yellow_0 @ (k2_yellow_1 @ X0) @ k1_xboole_0))
% 0.91/1.08          | (v1_xboole_0 @ X0))),
% 0.91/1.08      inference('clc', [status(thm)], ['75', '76'])).
% 0.91/1.08  thf('78', plain,
% 0.91/1.08      (![X34 : $i]:
% 0.91/1.08         ((m1_subset_1 @ (k3_yellow_0 @ X34) @ (u1_struct_0 @ X34))
% 0.91/1.08          | ~ (l1_orders_2 @ X34))),
% 0.91/1.08      inference('cnf', [status(esa)], [dt_k3_yellow_0])).
% 0.91/1.08  thf(t25_orders_2, axiom,
% 0.91/1.08    (![A:$i]:
% 0.91/1.08     ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.91/1.08       ( ![B:$i]:
% 0.91/1.08         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.91/1.08           ( ![C:$i]:
% 0.91/1.08             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.91/1.08               ( ( ( r1_orders_2 @ A @ B @ C ) & ( r1_orders_2 @ A @ C @ B ) ) =>
% 0.91/1.08                 ( ( B ) = ( C ) ) ) ) ) ) ) ))).
% 0.91/1.08  thf('79', plain,
% 0.91/1.08      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.91/1.08         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.91/1.08          | ~ (r1_orders_2 @ X15 @ X14 @ X16)
% 0.91/1.08          | ~ (r1_orders_2 @ X15 @ X16 @ X14)
% 0.91/1.08          | ((X14) = (X16))
% 0.91/1.08          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.91/1.08          | ~ (l1_orders_2 @ X15)
% 0.91/1.08          | ~ (v5_orders_2 @ X15))),
% 0.91/1.08      inference('cnf', [status(esa)], [t25_orders_2])).
% 0.91/1.08  thf('80', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         (~ (l1_orders_2 @ X0)
% 0.91/1.08          | ~ (v5_orders_2 @ X0)
% 0.91/1.08          | ~ (l1_orders_2 @ X0)
% 0.91/1.08          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.91/1.08          | ((k3_yellow_0 @ X0) = (X1))
% 0.91/1.08          | ~ (r1_orders_2 @ X0 @ X1 @ (k3_yellow_0 @ X0))
% 0.91/1.08          | ~ (r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ X1))),
% 0.91/1.08      inference('sup-', [status(thm)], ['78', '79'])).
% 0.91/1.08  thf('81', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         (~ (r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ X1)
% 0.91/1.08          | ~ (r1_orders_2 @ X0 @ X1 @ (k3_yellow_0 @ X0))
% 0.91/1.08          | ((k3_yellow_0 @ X0) = (X1))
% 0.91/1.08          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.91/1.08          | ~ (v5_orders_2 @ X0)
% 0.91/1.08          | ~ (l1_orders_2 @ X0))),
% 0.91/1.08      inference('simplify', [status(thm)], ['80'])).
% 0.91/1.08  thf('82', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         ((v1_xboole_0 @ X0)
% 0.91/1.08          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.91/1.08          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 0.91/1.08          | ~ (m1_subset_1 @ 
% 0.91/1.08               (k1_yellow_0 @ (k2_yellow_1 @ X0) @ k1_xboole_0) @ 
% 0.91/1.08               (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.91/1.08          | ((k3_yellow_0 @ (k2_yellow_1 @ X0))
% 0.91/1.08              = (k1_yellow_0 @ (k2_yellow_1 @ X0) @ k1_xboole_0))
% 0.91/1.08          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ 
% 0.91/1.08               (k1_yellow_0 @ (k2_yellow_1 @ X0) @ k1_xboole_0) @ 
% 0.91/1.08               (k3_yellow_0 @ (k2_yellow_1 @ X0))))),
% 0.91/1.08      inference('sup-', [status(thm)], ['77', '81'])).
% 0.91/1.08  thf('83', plain, (![X37 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X37))),
% 0.91/1.08      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.91/1.08  thf('84', plain, (![X41 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X41))),
% 0.91/1.08      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.91/1.08  thf('85', plain,
% 0.91/1.08      (![X42 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X42)) = (X42))),
% 0.91/1.08      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.91/1.08  thf('86', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         (m1_subset_1 @ (k1_yellow_0 @ (k2_yellow_1 @ X0) @ X1) @ X0)),
% 0.91/1.08      inference('demod', [status(thm)], ['71', '72'])).
% 0.91/1.08  thf('87', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         ((v1_xboole_0 @ X0)
% 0.91/1.08          | ((k3_yellow_0 @ (k2_yellow_1 @ X0))
% 0.91/1.08              = (k1_yellow_0 @ (k2_yellow_1 @ X0) @ k1_xboole_0))
% 0.91/1.08          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ 
% 0.91/1.08               (k1_yellow_0 @ (k2_yellow_1 @ X0) @ k1_xboole_0) @ 
% 0.91/1.08               (k3_yellow_0 @ (k2_yellow_1 @ X0))))),
% 0.91/1.08      inference('demod', [status(thm)], ['82', '83', '84', '85', '86'])).
% 0.91/1.08  thf('88', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         (~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ 
% 0.91/1.08             (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ 
% 0.91/1.08             (k3_yellow_0 @ (k2_yellow_1 @ X0)))
% 0.91/1.08          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.91/1.08          | ((k3_yellow_0 @ (k2_yellow_1 @ X0))
% 0.91/1.08              = (k1_yellow_0 @ (k2_yellow_1 @ X0) @ k1_xboole_0))
% 0.91/1.08          | (v1_xboole_0 @ X0))),
% 0.91/1.08      inference('sup-', [status(thm)], ['14', '87'])).
% 0.91/1.08  thf('89', plain, (![X37 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X37))),
% 0.91/1.08      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.91/1.08  thf('90', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         (~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ 
% 0.91/1.08             (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ 
% 0.91/1.08             (k3_yellow_0 @ (k2_yellow_1 @ X0)))
% 0.91/1.08          | ((k3_yellow_0 @ (k2_yellow_1 @ X0))
% 0.91/1.08              = (k1_yellow_0 @ (k2_yellow_1 @ X0) @ k1_xboole_0))
% 0.91/1.08          | (v1_xboole_0 @ X0))),
% 0.91/1.08      inference('demod', [status(thm)], ['88', '89'])).
% 0.91/1.08  thf('91', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         ((r1_orders_2 @ (k2_yellow_1 @ X0) @ 
% 0.91/1.08           (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ 
% 0.91/1.08           (k3_yellow_0 @ (k2_yellow_1 @ X0)))
% 0.91/1.08          | (v1_xboole_0 @ X0))),
% 0.91/1.08      inference('clc', [status(thm)], ['42', '49'])).
% 0.91/1.08  thf('92', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         ((v1_xboole_0 @ X0)
% 0.91/1.08          | ((k3_yellow_0 @ (k2_yellow_1 @ X0))
% 0.91/1.08              = (k1_yellow_0 @ (k2_yellow_1 @ X0) @ k1_xboole_0)))),
% 0.91/1.08      inference('clc', [status(thm)], ['90', '91'])).
% 0.91/1.08  thf(d9_yellow_0, axiom,
% 0.91/1.08    (![A:$i]:
% 0.91/1.08     ( ( l1_orders_2 @ A ) =>
% 0.91/1.08       ( ![B:$i,C:$i]:
% 0.91/1.08         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.91/1.08           ( ( r1_yellow_0 @ A @ B ) =>
% 0.91/1.08             ( ( ( C ) = ( k1_yellow_0 @ A @ B ) ) <=>
% 0.91/1.08               ( ( r2_lattice3 @ A @ B @ C ) & 
% 0.91/1.08                 ( ![D:$i]:
% 0.91/1.08                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.91/1.08                     ( ( r2_lattice3 @ A @ B @ D ) =>
% 0.91/1.08                       ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.91/1.08  thf('93', plain,
% 0.91/1.08      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.91/1.08         (((X30) != (k1_yellow_0 @ X28 @ X29))
% 0.91/1.08          | ~ (r2_lattice3 @ X28 @ X29 @ X31)
% 0.91/1.08          | (r1_orders_2 @ X28 @ X30 @ X31)
% 0.91/1.08          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X28))
% 0.91/1.08          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 0.91/1.08          | ~ (r1_yellow_0 @ X28 @ X29)
% 0.91/1.08          | ~ (l1_orders_2 @ X28))),
% 0.91/1.08      inference('cnf', [status(esa)], [d9_yellow_0])).
% 0.91/1.08  thf('94', plain,
% 0.91/1.08      (![X28 : $i, X29 : $i, X31 : $i]:
% 0.91/1.08         (~ (l1_orders_2 @ X28)
% 0.91/1.08          | ~ (r1_yellow_0 @ X28 @ X29)
% 0.91/1.08          | ~ (m1_subset_1 @ (k1_yellow_0 @ X28 @ X29) @ (u1_struct_0 @ X28))
% 0.91/1.08          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X28))
% 0.91/1.08          | (r1_orders_2 @ X28 @ (k1_yellow_0 @ X28 @ X29) @ X31)
% 0.91/1.08          | ~ (r2_lattice3 @ X28 @ X29 @ X31))),
% 0.91/1.08      inference('simplify', [status(thm)], ['93'])).
% 0.91/1.08  thf('95', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         (~ (m1_subset_1 @ (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ 
% 0.91/1.08             (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.91/1.08          | (v1_xboole_0 @ X0)
% 0.91/1.08          | ~ (r2_lattice3 @ (k2_yellow_1 @ X0) @ k1_xboole_0 @ X1)
% 0.91/1.08          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ 
% 0.91/1.08             (k1_yellow_0 @ (k2_yellow_1 @ X0) @ k1_xboole_0) @ X1)
% 0.91/1.08          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.91/1.08          | ~ (r1_yellow_0 @ (k2_yellow_1 @ X0) @ k1_xboole_0)
% 0.91/1.08          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.91/1.08      inference('sup-', [status(thm)], ['92', '94'])).
% 0.91/1.08  thf('96', plain,
% 0.91/1.08      (![X42 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X42)) = (X42))),
% 0.91/1.08      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.91/1.08  thf('97', plain,
% 0.91/1.08      (![X0 : $i]: (m1_subset_1 @ (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ X0)),
% 0.91/1.08      inference('demod', [status(thm)], ['21', '22'])).
% 0.91/1.08  thf('98', plain,
% 0.91/1.08      (![X42 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X42)) = (X42))),
% 0.91/1.08      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.91/1.08  thf('99', plain, (![X37 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X37))),
% 0.91/1.08      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.91/1.08  thf('100', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         ((v1_xboole_0 @ X0)
% 0.91/1.08          | ~ (r2_lattice3 @ (k2_yellow_1 @ X0) @ k1_xboole_0 @ X1)
% 0.91/1.08          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ 
% 0.91/1.08             (k1_yellow_0 @ (k2_yellow_1 @ X0) @ k1_xboole_0) @ X1)
% 0.91/1.08          | ~ (m1_subset_1 @ X1 @ X0)
% 0.91/1.08          | ~ (r1_yellow_0 @ (k2_yellow_1 @ X0) @ k1_xboole_0))),
% 0.91/1.08      inference('demod', [status(thm)], ['95', '96', '97', '98', '99'])).
% 0.91/1.08  thf('101', plain,
% 0.91/1.08      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.91/1.08        | ~ (r1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0)
% 0.91/1.08        | ~ (m1_subset_1 @ k1_xboole_0 @ sk_A)
% 0.91/1.08        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.91/1.08           (k1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0) @ k1_xboole_0)
% 0.91/1.08        | (v1_xboole_0 @ sk_A))),
% 0.91/1.08      inference('sup-', [status(thm)], ['13', '100'])).
% 0.91/1.08  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.91/1.08  thf('102', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.91/1.08      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.91/1.08  thf('103', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.91/1.08      inference('sup-', [status(thm)], ['3', '4'])).
% 0.91/1.08  thf('104', plain,
% 0.91/1.08      ((~ (r1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0)
% 0.91/1.08        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.91/1.08           (k1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0) @ k1_xboole_0)
% 0.91/1.08        | (v1_xboole_0 @ sk_A))),
% 0.91/1.08      inference('demod', [status(thm)], ['101', '102', '103'])).
% 0.91/1.08  thf('105', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.91/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.08  thf('106', plain,
% 0.91/1.08      (((r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.91/1.08         (k1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0) @ k1_xboole_0)
% 0.91/1.08        | ~ (r1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0))),
% 0.91/1.08      inference('clc', [status(thm)], ['104', '105'])).
% 0.91/1.08  thf('107', plain,
% 0.91/1.08      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.91/1.08        | ~ (v5_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.91/1.08        | ~ (v1_yellow_0 @ (k2_yellow_1 @ sk_A))
% 0.91/1.08        | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.91/1.08        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.91/1.08           (k1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0) @ k1_xboole_0))),
% 0.91/1.08      inference('sup-', [status(thm)], ['2', '106'])).
% 0.91/1.08  thf('108', plain, (![X41 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X41))),
% 0.91/1.08      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.91/1.08  thf('109', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.91/1.08      inference('sup-', [status(thm)], ['3', '4'])).
% 0.91/1.08  thf('110', plain,
% 0.91/1.08      (![X42 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X42)) = (X42))),
% 0.91/1.08      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.91/1.08  thf(d8_lattice3, axiom,
% 0.91/1.08    (![A:$i]:
% 0.91/1.08     ( ( l1_orders_2 @ A ) =>
% 0.91/1.08       ( ![B:$i,C:$i]:
% 0.91/1.08         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.91/1.08           ( ( r1_lattice3 @ A @ B @ C ) <=>
% 0.91/1.08             ( ![D:$i]:
% 0.91/1.08               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.91/1.08                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ))).
% 0.91/1.08  thf('111', plain,
% 0.91/1.08      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.91/1.08         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 0.91/1.08          | (r2_hidden @ (sk_D @ X17 @ X19 @ X18) @ X19)
% 0.91/1.08          | (r1_lattice3 @ X18 @ X19 @ X17)
% 0.91/1.08          | ~ (l1_orders_2 @ X18))),
% 0.91/1.08      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.91/1.08  thf('112', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.08         (~ (m1_subset_1 @ X1 @ X0)
% 0.91/1.08          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.91/1.08          | (r1_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.91/1.08          | (r2_hidden @ (sk_D @ X1 @ X2 @ (k2_yellow_1 @ X0)) @ X2))),
% 0.91/1.08      inference('sup-', [status(thm)], ['110', '111'])).
% 0.91/1.08  thf('113', plain, (![X37 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X37))),
% 0.91/1.08      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.91/1.08  thf('114', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.08         (~ (m1_subset_1 @ X1 @ X0)
% 0.91/1.08          | (r1_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.91/1.08          | (r2_hidden @ (sk_D @ X1 @ X2 @ (k2_yellow_1 @ X0)) @ X2))),
% 0.91/1.08      inference('demod', [status(thm)], ['112', '113'])).
% 0.91/1.08  thf('115', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ (k2_yellow_1 @ sk_A)) @ X0)
% 0.91/1.08          | (r1_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ k1_xboole_0))),
% 0.91/1.08      inference('sup-', [status(thm)], ['109', '114'])).
% 0.91/1.08  thf('116', plain,
% 0.91/1.08      (![X7 : $i, X8 : $i]: ((m1_subset_1 @ X7 @ X8) | ~ (r2_hidden @ X7 @ X8))),
% 0.91/1.08      inference('cnf', [status(esa)], [t1_subset])).
% 0.91/1.08  thf('117', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         ((r1_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ k1_xboole_0)
% 0.91/1.08          | (m1_subset_1 @ (sk_D @ k1_xboole_0 @ X0 @ (k2_yellow_1 @ sk_A)) @ 
% 0.91/1.08             X0))),
% 0.91/1.08      inference('sup-', [status(thm)], ['115', '116'])).
% 0.91/1.08  thf('118', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         ((r1_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ k1_xboole_0)
% 0.91/1.08          | (m1_subset_1 @ (sk_D @ k1_xboole_0 @ X0 @ (k2_yellow_1 @ sk_A)) @ 
% 0.91/1.08             X0))),
% 0.91/1.08      inference('sup-', [status(thm)], ['115', '116'])).
% 0.91/1.08  thf('119', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.91/1.08      inference('sup-', [status(thm)], ['3', '4'])).
% 0.91/1.08  thf('120', plain,
% 0.91/1.08      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.91/1.08         (~ (m1_subset_1 @ X44 @ X45)
% 0.91/1.08          | ~ (r1_tarski @ X44 @ X46)
% 0.91/1.08          | (r3_orders_2 @ (k2_yellow_1 @ X45) @ X44 @ X46)
% 0.91/1.08          | ~ (m1_subset_1 @ X46 @ X45)
% 0.91/1.08          | (v1_xboole_0 @ X45))),
% 0.91/1.08      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.91/1.08  thf('121', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         ((v1_xboole_0 @ sk_A)
% 0.91/1.08          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.91/1.08          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ X0)
% 0.91/1.08          | ~ (r1_tarski @ k1_xboole_0 @ X0))),
% 0.91/1.08      inference('sup-', [status(thm)], ['119', '120'])).
% 0.91/1.08  thf('122', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.91/1.08      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.91/1.08  thf('123', plain,
% 0.91/1.08      (![X4 : $i, X6 : $i]:
% 0.91/1.08         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.91/1.08      inference('cnf', [status(esa)], [d3_tarski])).
% 0.91/1.08  thf('124', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.91/1.08      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.91/1.08  thf('125', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.91/1.08      inference('sup-', [status(thm)], ['123', '124'])).
% 0.91/1.08  thf('126', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.91/1.08      inference('sup-', [status(thm)], ['122', '125'])).
% 0.91/1.08  thf('127', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         ((v1_xboole_0 @ sk_A)
% 0.91/1.08          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.91/1.08          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ X0))),
% 0.91/1.08      inference('demod', [status(thm)], ['121', '126'])).
% 0.91/1.08  thf('128', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.91/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.08  thf('129', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         ((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ X0)
% 0.91/1.08          | ~ (m1_subset_1 @ X0 @ sk_A))),
% 0.91/1.08      inference('clc', [status(thm)], ['127', '128'])).
% 0.91/1.08  thf('130', plain,
% 0.91/1.08      (((r1_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_A @ k1_xboole_0)
% 0.91/1.08        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.91/1.08           (sk_D @ k1_xboole_0 @ sk_A @ (k2_yellow_1 @ sk_A))))),
% 0.91/1.08      inference('sup-', [status(thm)], ['118', '129'])).
% 0.91/1.08  thf('131', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.08         (~ (m1_subset_1 @ X1 @ X0)
% 0.91/1.08          | ~ (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.91/1.08          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.91/1.08          | ~ (m1_subset_1 @ X2 @ X0)
% 0.91/1.08          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.91/1.08      inference('demod', [status(thm)], ['34', '35', '36', '37'])).
% 0.91/1.08  thf('132', plain,
% 0.91/1.08      (((r1_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_A @ k1_xboole_0)
% 0.91/1.08        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.91/1.08        | ~ (m1_subset_1 @ 
% 0.91/1.08             (sk_D @ k1_xboole_0 @ sk_A @ (k2_yellow_1 @ sk_A)) @ sk_A)
% 0.91/1.08        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.91/1.08           (sk_D @ k1_xboole_0 @ sk_A @ (k2_yellow_1 @ sk_A)))
% 0.91/1.08        | ~ (m1_subset_1 @ k1_xboole_0 @ sk_A))),
% 0.91/1.08      inference('sup-', [status(thm)], ['130', '131'])).
% 0.91/1.08  thf('133', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.91/1.08      inference('sup-', [status(thm)], ['3', '4'])).
% 0.91/1.08  thf('134', plain,
% 0.91/1.08      (((r1_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_A @ k1_xboole_0)
% 0.91/1.08        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.91/1.08        | ~ (m1_subset_1 @ 
% 0.91/1.08             (sk_D @ k1_xboole_0 @ sk_A @ (k2_yellow_1 @ sk_A)) @ sk_A)
% 0.91/1.08        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.91/1.08           (sk_D @ k1_xboole_0 @ sk_A @ (k2_yellow_1 @ sk_A))))),
% 0.91/1.08      inference('demod', [status(thm)], ['132', '133'])).
% 0.91/1.08  thf('135', plain,
% 0.91/1.08      (((r1_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_A @ k1_xboole_0)
% 0.91/1.08        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.91/1.08           (sk_D @ k1_xboole_0 @ sk_A @ (k2_yellow_1 @ sk_A)))
% 0.91/1.08        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.91/1.08        | (r1_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_A @ k1_xboole_0))),
% 0.91/1.08      inference('sup-', [status(thm)], ['117', '134'])).
% 0.91/1.08  thf('136', plain,
% 0.91/1.08      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.91/1.08        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.91/1.08           (sk_D @ k1_xboole_0 @ sk_A @ (k2_yellow_1 @ sk_A)))
% 0.91/1.08        | (r1_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_A @ k1_xboole_0))),
% 0.91/1.08      inference('simplify', [status(thm)], ['135'])).
% 0.91/1.08  thf('137', plain,
% 0.91/1.08      (![X42 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X42)) = (X42))),
% 0.91/1.08      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.91/1.08  thf('138', plain,
% 0.91/1.08      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.91/1.08         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 0.91/1.08          | ~ (r1_orders_2 @ X18 @ X17 @ (sk_D @ X17 @ X19 @ X18))
% 0.91/1.08          | (r1_lattice3 @ X18 @ X19 @ X17)
% 0.91/1.08          | ~ (l1_orders_2 @ X18))),
% 0.91/1.08      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.91/1.08  thf('139', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.08         (~ (m1_subset_1 @ X1 @ X0)
% 0.91/1.08          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.91/1.08          | (r1_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.91/1.08          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ 
% 0.91/1.08               (sk_D @ X1 @ X2 @ (k2_yellow_1 @ X0))))),
% 0.91/1.08      inference('sup-', [status(thm)], ['137', '138'])).
% 0.91/1.08  thf('140', plain, (![X37 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X37))),
% 0.91/1.08      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.91/1.08  thf('141', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.08         (~ (m1_subset_1 @ X1 @ X0)
% 0.91/1.08          | (r1_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.91/1.08          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ 
% 0.91/1.08               (sk_D @ X1 @ X2 @ (k2_yellow_1 @ X0))))),
% 0.91/1.08      inference('demod', [status(thm)], ['139', '140'])).
% 0.91/1.08  thf('142', plain,
% 0.91/1.08      (((r1_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_A @ k1_xboole_0)
% 0.91/1.08        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.91/1.08        | (r1_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_A @ k1_xboole_0)
% 0.91/1.08        | ~ (m1_subset_1 @ k1_xboole_0 @ sk_A))),
% 0.91/1.08      inference('sup-', [status(thm)], ['136', '141'])).
% 0.91/1.08  thf('143', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.91/1.08      inference('sup-', [status(thm)], ['3', '4'])).
% 0.91/1.08  thf('144', plain,
% 0.91/1.08      (((r1_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_A @ k1_xboole_0)
% 0.91/1.08        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.91/1.08        | (r1_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_A @ k1_xboole_0))),
% 0.91/1.08      inference('demod', [status(thm)], ['142', '143'])).
% 0.91/1.08  thf('145', plain,
% 0.91/1.08      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.91/1.08        | (r1_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_A @ k1_xboole_0))),
% 0.91/1.08      inference('simplify', [status(thm)], ['144'])).
% 0.91/1.08  thf('146', plain,
% 0.91/1.08      (![X42 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X42)) = (X42))),
% 0.91/1.08      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.91/1.08  thf(d4_yellow_0, axiom,
% 0.91/1.08    (![A:$i]:
% 0.91/1.08     ( ( l1_orders_2 @ A ) =>
% 0.91/1.08       ( ( v1_yellow_0 @ A ) <=>
% 0.91/1.08         ( ?[B:$i]:
% 0.91/1.08           ( ( r1_lattice3 @ A @ ( u1_struct_0 @ A ) @ B ) & 
% 0.91/1.08             ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.91/1.08  thf('147', plain,
% 0.91/1.08      (![X26 : $i, X27 : $i]:
% 0.91/1.08         (~ (r1_lattice3 @ X26 @ (u1_struct_0 @ X26) @ X27)
% 0.91/1.08          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X26))
% 0.91/1.08          | (v1_yellow_0 @ X26)
% 0.91/1.08          | ~ (l1_orders_2 @ X26))),
% 0.91/1.08      inference('cnf', [status(esa)], [d4_yellow_0])).
% 0.91/1.08  thf('148', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         (~ (r1_lattice3 @ (k2_yellow_1 @ X0) @ X0 @ X1)
% 0.91/1.08          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.91/1.08          | (v1_yellow_0 @ (k2_yellow_1 @ X0))
% 0.91/1.08          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k2_yellow_1 @ X0))))),
% 0.91/1.08      inference('sup-', [status(thm)], ['146', '147'])).
% 0.91/1.08  thf('149', plain, (![X37 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X37))),
% 0.91/1.08      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.91/1.08  thf('150', plain,
% 0.91/1.08      (![X42 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X42)) = (X42))),
% 0.91/1.08      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.91/1.08  thf('151', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         (~ (r1_lattice3 @ (k2_yellow_1 @ X0) @ X0 @ X1)
% 0.91/1.08          | (v1_yellow_0 @ (k2_yellow_1 @ X0))
% 0.91/1.08          | ~ (m1_subset_1 @ X1 @ X0))),
% 0.91/1.08      inference('demod', [status(thm)], ['148', '149', '150'])).
% 0.91/1.08  thf('152', plain,
% 0.91/1.08      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.91/1.08        | ~ (m1_subset_1 @ k1_xboole_0 @ sk_A)
% 0.91/1.08        | (v1_yellow_0 @ (k2_yellow_1 @ sk_A)))),
% 0.91/1.08      inference('sup-', [status(thm)], ['145', '151'])).
% 0.91/1.08  thf('153', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.91/1.08      inference('sup-', [status(thm)], ['3', '4'])).
% 0.91/1.08  thf('154', plain,
% 0.91/1.08      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.91/1.08        | (v1_yellow_0 @ (k2_yellow_1 @ sk_A)))),
% 0.91/1.08      inference('demod', [status(thm)], ['152', '153'])).
% 0.91/1.08  thf('155', plain, (![X37 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X37))),
% 0.91/1.08      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.91/1.08  thf('156', plain,
% 0.91/1.08      (![X9 : $i]:
% 0.91/1.08         ((v1_xboole_0 @ (u1_struct_0 @ X9))
% 0.91/1.08          | ~ (l1_struct_0 @ X9)
% 0.91/1.08          | ~ (v2_struct_0 @ X9))),
% 0.91/1.08      inference('cnf', [status(esa)], [fc1_struct_0])).
% 0.91/1.08  thf('157', plain,
% 0.91/1.08      (![X34 : $i]:
% 0.91/1.08         ((m1_subset_1 @ (k3_yellow_0 @ X34) @ (u1_struct_0 @ X34))
% 0.91/1.08          | ~ (l1_orders_2 @ X34))),
% 0.91/1.08      inference('cnf', [status(esa)], [dt_k3_yellow_0])).
% 0.91/1.08  thf('158', plain,
% 0.91/1.08      (![X34 : $i]:
% 0.91/1.08         ((m1_subset_1 @ (k3_yellow_0 @ X34) @ (u1_struct_0 @ X34))
% 0.91/1.08          | ~ (l1_orders_2 @ X34))),
% 0.91/1.08      inference('cnf', [status(esa)], [dt_k3_yellow_0])).
% 0.91/1.08  thf('159', plain,
% 0.91/1.08      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.91/1.08         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 0.91/1.08          | (r2_hidden @ (sk_D @ X17 @ X19 @ X18) @ X19)
% 0.91/1.08          | (r1_lattice3 @ X18 @ X19 @ X17)
% 0.91/1.08          | ~ (l1_orders_2 @ X18))),
% 0.91/1.08      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.91/1.08  thf('160', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         (~ (l1_orders_2 @ X0)
% 0.91/1.08          | ~ (l1_orders_2 @ X0)
% 0.91/1.08          | (r1_lattice3 @ X0 @ X1 @ (k3_yellow_0 @ X0))
% 0.91/1.08          | (r2_hidden @ (sk_D @ (k3_yellow_0 @ X0) @ X1 @ X0) @ X1))),
% 0.91/1.08      inference('sup-', [status(thm)], ['158', '159'])).
% 0.91/1.08  thf('161', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         ((r2_hidden @ (sk_D @ (k3_yellow_0 @ X0) @ X1 @ X0) @ X1)
% 0.91/1.08          | (r1_lattice3 @ X0 @ X1 @ (k3_yellow_0 @ X0))
% 0.91/1.08          | ~ (l1_orders_2 @ X0))),
% 0.91/1.08      inference('simplify', [status(thm)], ['160'])).
% 0.91/1.08  thf('162', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.91/1.08      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.91/1.08  thf('163', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         (~ (l1_orders_2 @ X1)
% 0.91/1.08          | (r1_lattice3 @ X1 @ X0 @ (k3_yellow_0 @ X1))
% 0.91/1.08          | ~ (v1_xboole_0 @ X0))),
% 0.91/1.08      inference('sup-', [status(thm)], ['161', '162'])).
% 0.91/1.08  thf('164', plain,
% 0.91/1.08      (![X26 : $i, X27 : $i]:
% 0.91/1.08         (~ (r1_lattice3 @ X26 @ (u1_struct_0 @ X26) @ X27)
% 0.91/1.08          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X26))
% 0.91/1.08          | (v1_yellow_0 @ X26)
% 0.91/1.08          | ~ (l1_orders_2 @ X26))),
% 0.91/1.08      inference('cnf', [status(esa)], [d4_yellow_0])).
% 0.91/1.08  thf('165', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         (~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.91/1.08          | ~ (l1_orders_2 @ X0)
% 0.91/1.08          | ~ (l1_orders_2 @ X0)
% 0.91/1.08          | (v1_yellow_0 @ X0)
% 0.91/1.08          | ~ (m1_subset_1 @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0)))),
% 0.91/1.08      inference('sup-', [status(thm)], ['163', '164'])).
% 0.91/1.08  thf('166', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         (~ (m1_subset_1 @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0))
% 0.91/1.08          | (v1_yellow_0 @ X0)
% 0.91/1.08          | ~ (l1_orders_2 @ X0)
% 0.91/1.08          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.91/1.08      inference('simplify', [status(thm)], ['165'])).
% 0.91/1.08  thf('167', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         (~ (l1_orders_2 @ X0)
% 0.91/1.08          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.91/1.08          | ~ (l1_orders_2 @ X0)
% 0.91/1.08          | (v1_yellow_0 @ X0))),
% 0.91/1.08      inference('sup-', [status(thm)], ['157', '166'])).
% 0.91/1.08  thf('168', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         ((v1_yellow_0 @ X0)
% 0.91/1.08          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.91/1.08          | ~ (l1_orders_2 @ X0))),
% 0.91/1.08      inference('simplify', [status(thm)], ['167'])).
% 0.91/1.08  thf('169', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         (~ (v2_struct_0 @ X0)
% 0.91/1.08          | ~ (l1_struct_0 @ X0)
% 0.91/1.08          | ~ (l1_orders_2 @ X0)
% 0.91/1.08          | (v1_yellow_0 @ X0))),
% 0.91/1.08      inference('sup-', [status(thm)], ['156', '168'])).
% 0.91/1.08  thf('170', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         ((v1_yellow_0 @ (k2_yellow_1 @ X0))
% 0.91/1.08          | ~ (l1_struct_0 @ (k2_yellow_1 @ X0))
% 0.91/1.08          | ~ (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.91/1.08      inference('sup-', [status(thm)], ['155', '169'])).
% 0.91/1.08  thf('171', plain, (![X0 : $i]: (l1_struct_0 @ (k2_yellow_1 @ X0))),
% 0.91/1.08      inference('sup-', [status(thm)], ['46', '47'])).
% 0.91/1.08  thf('172', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         ((v1_yellow_0 @ (k2_yellow_1 @ X0))
% 0.91/1.08          | ~ (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.91/1.08      inference('demod', [status(thm)], ['170', '171'])).
% 0.91/1.08  thf('173', plain, ((v1_yellow_0 @ (k2_yellow_1 @ sk_A))),
% 0.91/1.08      inference('clc', [status(thm)], ['154', '172'])).
% 0.91/1.08  thf('174', plain, (![X37 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X37))),
% 0.91/1.08      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.91/1.08  thf('175', plain,
% 0.91/1.08      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.91/1.08        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.91/1.08           (k1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0) @ k1_xboole_0))),
% 0.91/1.08      inference('demod', [status(thm)], ['107', '108', '173', '174'])).
% 0.91/1.08  thf('176', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         (m1_subset_1 @ (k1_yellow_0 @ (k2_yellow_1 @ X0) @ X1) @ X0)),
% 0.91/1.08      inference('demod', [status(thm)], ['71', '72'])).
% 0.91/1.08  thf('177', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         ((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ X0)
% 0.91/1.08          | ~ (m1_subset_1 @ X0 @ sk_A))),
% 0.91/1.08      inference('clc', [status(thm)], ['127', '128'])).
% 0.91/1.08  thf('178', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.91/1.08          (k1_yellow_0 @ (k2_yellow_1 @ sk_A) @ X0))),
% 0.91/1.08      inference('sup-', [status(thm)], ['176', '177'])).
% 0.91/1.08  thf('179', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.08         (~ (m1_subset_1 @ X1 @ X0)
% 0.91/1.08          | ~ (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.91/1.08          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.91/1.08          | ~ (m1_subset_1 @ X2 @ X0)
% 0.91/1.08          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.91/1.08      inference('demod', [status(thm)], ['34', '35', '36', '37'])).
% 0.91/1.08  thf('180', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         ((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.91/1.08          | ~ (m1_subset_1 @ (k1_yellow_0 @ (k2_yellow_1 @ sk_A) @ X0) @ sk_A)
% 0.91/1.08          | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.91/1.08             (k1_yellow_0 @ (k2_yellow_1 @ sk_A) @ X0))
% 0.91/1.08          | ~ (m1_subset_1 @ k1_xboole_0 @ sk_A))),
% 0.91/1.08      inference('sup-', [status(thm)], ['178', '179'])).
% 0.91/1.08  thf('181', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         (m1_subset_1 @ (k1_yellow_0 @ (k2_yellow_1 @ X0) @ X1) @ X0)),
% 0.91/1.08      inference('demod', [status(thm)], ['71', '72'])).
% 0.91/1.08  thf('182', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.91/1.08      inference('sup-', [status(thm)], ['3', '4'])).
% 0.91/1.08  thf('183', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         ((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.91/1.08          | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0 @ 
% 0.91/1.08             (k1_yellow_0 @ (k2_yellow_1 @ sk_A) @ X0)))),
% 0.91/1.08      inference('demod', [status(thm)], ['180', '181', '182'])).
% 0.91/1.08  thf('184', plain,
% 0.91/1.08      (![X42 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X42)) = (X42))),
% 0.91/1.08      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.91/1.08  thf('185', plain,
% 0.91/1.08      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.91/1.08         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.91/1.08          | ~ (r1_orders_2 @ X15 @ X14 @ X16)
% 0.91/1.08          | ~ (r1_orders_2 @ X15 @ X16 @ X14)
% 0.91/1.08          | ((X14) = (X16))
% 0.91/1.08          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.91/1.08          | ~ (l1_orders_2 @ X15)
% 0.91/1.08          | ~ (v5_orders_2 @ X15))),
% 0.91/1.08      inference('cnf', [status(esa)], [t25_orders_2])).
% 0.91/1.08  thf('186', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.08         (~ (m1_subset_1 @ X1 @ X0)
% 0.91/1.08          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 0.91/1.08          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.91/1.08          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.91/1.08          | ((X1) = (X2))
% 0.91/1.08          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.91/1.08          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2))),
% 0.91/1.08      inference('sup-', [status(thm)], ['184', '185'])).
% 0.91/1.08  thf('187', plain, (![X41 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X41))),
% 0.91/1.08      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.91/1.08  thf('188', plain, (![X37 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X37))),
% 0.91/1.08      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.91/1.08  thf('189', plain,
% 0.91/1.08      (![X42 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X42)) = (X42))),
% 0.91/1.08      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.91/1.08  thf('190', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.08         (~ (m1_subset_1 @ X1 @ X0)
% 0.91/1.08          | ~ (m1_subset_1 @ X2 @ X0)
% 0.91/1.08          | ((X1) = (X2))
% 0.91/1.08          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.91/1.08          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2))),
% 0.91/1.08      inference('demod', [status(thm)], ['186', '187', '188', '189'])).
% 0.91/1.08  thf('191', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         ((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.91/1.08          | ~ (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.91/1.08               (k1_yellow_0 @ (k2_yellow_1 @ sk_A) @ X0) @ k1_xboole_0)
% 0.91/1.08          | ((k1_yellow_0 @ (k2_yellow_1 @ sk_A) @ X0) = (k1_xboole_0))
% 0.91/1.08          | ~ (m1_subset_1 @ k1_xboole_0 @ sk_A)
% 0.91/1.08          | ~ (m1_subset_1 @ (k1_yellow_0 @ (k2_yellow_1 @ sk_A) @ X0) @ sk_A))),
% 0.91/1.08      inference('sup-', [status(thm)], ['183', '190'])).
% 0.91/1.08  thf('192', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.91/1.08      inference('sup-', [status(thm)], ['3', '4'])).
% 0.91/1.08  thf('193', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         (m1_subset_1 @ (k1_yellow_0 @ (k2_yellow_1 @ X0) @ X1) @ X0)),
% 0.91/1.08      inference('demod', [status(thm)], ['71', '72'])).
% 0.91/1.08  thf('194', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         ((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.91/1.08          | ~ (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.91/1.08               (k1_yellow_0 @ (k2_yellow_1 @ sk_A) @ X0) @ k1_xboole_0)
% 0.91/1.08          | ((k1_yellow_0 @ (k2_yellow_1 @ sk_A) @ X0) = (k1_xboole_0)))),
% 0.91/1.08      inference('demod', [status(thm)], ['191', '192', '193'])).
% 0.91/1.08  thf('195', plain,
% 0.91/1.08      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.91/1.08        | ((k1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0) = (k1_xboole_0))
% 0.91/1.08        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.91/1.08      inference('sup-', [status(thm)], ['175', '194'])).
% 0.91/1.08  thf('196', plain,
% 0.91/1.08      ((((k1_yellow_0 @ (k2_yellow_1 @ sk_A) @ k1_xboole_0) = (k1_xboole_0))
% 0.91/1.08        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.91/1.08      inference('simplify', [status(thm)], ['195'])).
% 0.91/1.08  thf('197', plain,
% 0.91/1.08      ((((k3_yellow_0 @ (k2_yellow_1 @ sk_A)) = (k1_xboole_0))
% 0.91/1.08        | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.91/1.08        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.91/1.08      inference('sup+', [status(thm)], ['1', '196'])).
% 0.91/1.08  thf('198', plain, (![X37 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X37))),
% 0.91/1.08      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.91/1.08  thf('199', plain,
% 0.91/1.08      ((((k3_yellow_0 @ (k2_yellow_1 @ sk_A)) = (k1_xboole_0))
% 0.91/1.08        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.91/1.08      inference('demod', [status(thm)], ['197', '198'])).
% 0.91/1.08  thf('200', plain, (((k3_yellow_0 @ (k2_yellow_1 @ sk_A)) != (k1_xboole_0))),
% 0.91/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.08  thf('201', plain, ((v2_struct_0 @ (k2_yellow_1 @ sk_A))),
% 0.91/1.08      inference('simplify_reflect-', [status(thm)], ['199', '200'])).
% 0.91/1.08  thf('202', plain,
% 0.91/1.08      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.91/1.08      inference('demod', [status(thm)], ['45', '48'])).
% 0.91/1.08  thf('203', plain, ((v1_xboole_0 @ sk_A)),
% 0.91/1.08      inference('sup-', [status(thm)], ['201', '202'])).
% 0.91/1.08  thf('204', plain, ($false), inference('demod', [status(thm)], ['0', '203'])).
% 0.91/1.08  
% 0.91/1.08  % SZS output end Refutation
% 0.91/1.08  
% 0.91/1.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
