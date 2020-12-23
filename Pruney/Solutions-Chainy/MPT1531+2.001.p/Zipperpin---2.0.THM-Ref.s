%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cTDAbHYjDB

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:42 EST 2020

% Result     : Theorem 3.31s
% Output     : Refutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 333 expanded)
%              Number of leaves         :   25 ( 102 expanded)
%              Depth                    :   17
%              Number of atoms          : 1082 (4567 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t9_yellow_0,conjecture,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
             => ( ( ( r1_lattice3 @ A @ C @ D )
                 => ( r1_lattice3 @ A @ B @ D ) )
                & ( ( r2_lattice3 @ A @ C @ D )
                 => ( r2_lattice3 @ A @ B @ D ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_orders_2 @ A )
       => ! [B: $i,C: $i] :
            ( ( r1_tarski @ B @ C )
           => ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ( ( ( r1_lattice3 @ A @ C @ D )
                   => ( r1_lattice3 @ A @ B @ D ) )
                  & ( ( r2_lattice3 @ A @ C @ D )
                   => ( r2_lattice3 @ A @ B @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t9_yellow_0])).

thf('0',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('3',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_B_1 @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 )
   <= ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('6',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X36 ) )
      | ( r2_hidden @ ( sk_D_1 @ X35 @ X37 @ X36 ) @ X37 )
      | ( r2_lattice3 @ X36 @ X37 @ X35 )
      | ~ ( l1_orders_2 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X18: $i,X20: $i] :
      ( ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('13',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( m1_subset_1 @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B_1 @ sk_D_2 )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_B_1 @ sk_A ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r2_hidden @ X16 @ X17 )
      | ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('17',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B_1 @ sk_D_2 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B_1 @ sk_A ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X36 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X35 @ X37 @ X36 ) @ ( u1_struct_0 @ X36 ) )
      | ( r2_lattice3 @ X36 @ X37 @ X35 )
      | ~ ( l1_orders_2 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X36 ) )
      | ~ ( r2_lattice3 @ X36 @ X37 @ X35 )
      | ~ ( r2_hidden @ X38 @ X37 )
      | ( r1_orders_2 @ X36 @ X38 @ X35 )
      | ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X36 ) )
      | ~ ( l1_orders_2 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r2_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_A ) @ X1 )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_A ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( r2_lattice3 @ sk_A @ sk_B_1 @ sk_D_2 )
    | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_D_2 @ sk_B_1 @ sk_A ) @ sk_D_2 )
    | ~ ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_B_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['17','28'])).

thf('30',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 )
    | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_D_2 @ sk_B_1 @ sk_A ) @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_B_1 @ sk_D_2 )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( r2_lattice3 @ sk_A @ sk_B_1 @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_D_2 @ sk_B_1 @ sk_A ) @ sk_D_2 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['4','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X36 ) )
      | ~ ( r1_orders_2 @ X36 @ ( sk_D_1 @ X35 @ X37 @ X36 ) @ X35 )
      | ( r2_lattice3 @ X36 @ X37 @ X35 )
      | ~ ( l1_orders_2 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_A ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_A ) @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_B_1 @ sk_D_2 )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 ) ),
    inference(clc,[status(thm)],['31','36'])).

thf('38',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_B_1 @ sk_D_2 )
    | ~ ( r2_lattice3 @ sk_A @ sk_B_1 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_B_1 @ sk_D_2 )
   <= ~ ( r2_lattice3 @ sk_A @ sk_B_1 @ sk_D_2 ) ),
    inference(split,[status(esa)],['38'])).

thf('40',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
   <= ( ~ ( r2_lattice3 @ sk_A @ sk_B_1 @ sk_D_2 )
      & ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('42',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ~ ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_B_1 )
   <= ( ~ ( r2_lattice3 @ sk_A @ sk_B_1 @ sk_D_2 )
      & ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( ~ ( r2_lattice3 @ sk_A @ sk_B_1 @ sk_D_2 )
      & ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['2','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_B_1 @ sk_D_2 )
   <= ~ ( r2_lattice3 @ sk_A @ sk_B_1 @ sk_D_2 ) ),
    inference(split,[status(esa)],['38'])).

thf('50',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
   <= ~ ( r2_lattice3 @ sk_A @ sk_B_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( $false
   <= ( ~ ( r2_lattice3 @ sk_A @ sk_B_1 @ sk_D_2 )
      & ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['45','50'])).

thf('52',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_B_1 @ sk_D_2 )
    | ~ ( r1_lattice3 @ sk_A @ sk_B_1 @ sk_D_2 ) ),
    inference(split,[status(esa)],['38'])).

thf('53',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 )
    | ~ ( r2_lattice3 @ sk_A @ sk_B_1 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 )
    | ~ ( r2_lattice3 @ sk_A @ sk_B_1 @ sk_D_2 ) ),
    inference(split,[status(esa)],['53'])).

thf('55',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('56',plain,
    ( ( r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 )
   <= ( r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 ) ),
    inference(split,[status(esa)],['53'])).

thf('57',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('58',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ( r2_hidden @ ( sk_D @ X31 @ X33 @ X32 ) @ X33 )
      | ( r1_lattice3 @ X32 @ X33 @ X31 )
      | ~ ( l1_orders_2 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('63',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B_1 @ sk_D_2 )
    | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_B_1 @ sk_A ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r2_hidden @ X16 @ X17 )
      | ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('65',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B_1 @ sk_D_2 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_2 @ sk_B_1 @ sk_A ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ( m1_subset_1 @ ( sk_D @ X31 @ X33 @ X32 ) @ ( u1_struct_0 @ X32 ) )
      | ( r1_lattice3 @ X32 @ X33 @ X31 )
      | ~ ( l1_orders_2 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ~ ( r1_lattice3 @ X32 @ X33 @ X31 )
      | ~ ( r2_hidden @ X34 @ X33 )
      | ( r1_orders_2 @ X32 @ X31 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X32 ) )
      | ~ ( l1_orders_2 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_lattice3 @ sk_A @ X1 @ sk_D_2 )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X1 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['70','75'])).

thf('77',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( r1_lattice3 @ sk_A @ sk_B_1 @ sk_D_2 )
    | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_B_1 @ sk_A ) )
    | ~ ( r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 )
    | ( r1_lattice3 @ sk_A @ sk_B_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['65','76'])).

thf('78',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 )
    | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_B_1 @ sk_A ) )
    | ( r1_lattice3 @ sk_A @ sk_B_1 @ sk_D_2 )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( r1_lattice3 @ sk_A @ sk_B_1 @ sk_D_2 )
      | ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_B_1 @ sk_A ) ) )
   <= ( r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['56','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_D_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ~ ( r1_orders_2 @ X32 @ X31 @ ( sk_D @ X31 @ X33 @ X32 ) )
      | ( r1_lattice3 @ X32 @ X33 @ X31 )
      | ~ ( l1_orders_2 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( r1_orders_2 @ sk_A @ sk_D_2 @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ( r1_lattice3 @ sk_A @ sk_B_1 @ sk_D_2 )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 ) ),
    inference(clc,[status(thm)],['79','84'])).

thf('86',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_B_1 @ sk_D_2 )
   <= ~ ( r1_lattice3 @ sk_A @ sk_B_1 @ sk_D_2 ) ),
    inference(split,[status(esa)],['38'])).

thf('87',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
   <= ( ~ ( r1_lattice3 @ sk_A @ sk_B_1 @ sk_D_2 )
      & ( r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('89',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_B_1 )
   <= ( ~ ( r1_lattice3 @ sk_A @ sk_B_1 @ sk_D_2 )
      & ( r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( ~ ( r1_lattice3 @ sk_A @ sk_B_1 @ sk_D_2 )
      & ( r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['55','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_D_2 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_B_1 @ sk_D_2 )
   <= ~ ( r1_lattice3 @ sk_A @ sk_B_1 @ sk_D_2 ) ),
    inference(split,[status(esa)],['38'])).

thf('95',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
   <= ~ ( r1_lattice3 @ sk_A @ sk_B_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( r1_lattice3 @ sk_A @ sk_B_1 @ sk_D_2 )
    | ~ ( r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['90','95'])).

thf('97',plain,(
    ~ ( r2_lattice3 @ sk_A @ sk_B_1 @ sk_D_2 ) ),
    inference('sat_resolution*',[status(thm)],['52','54','96'])).

thf('98',plain,(
    ~ ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 ) ),
    inference(simpl_trail,[status(thm)],['51','97'])).

thf('99',plain,
    ( ~ ( r1_lattice3 @ sk_A @ sk_B_1 @ sk_D_2 )
    | ( r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2 ) ),
    inference(split,[status(esa)],['3'])).

thf('100',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','98','99','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cTDAbHYjDB
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:50:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.31/3.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.31/3.56  % Solved by: fo/fo7.sh
% 3.31/3.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.31/3.56  % done 3752 iterations in 3.109s
% 3.31/3.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.31/3.56  % SZS output start Refutation
% 3.31/3.56  thf(sk_D_2_type, type, sk_D_2: $i).
% 3.31/3.56  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 3.31/3.56  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 3.31/3.56  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 3.31/3.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 3.31/3.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.31/3.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.31/3.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.31/3.56  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 3.31/3.56  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 3.31/3.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.31/3.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.31/3.56  thf(sk_B_type, type, sk_B: $i > $i).
% 3.31/3.56  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 3.31/3.56  thf(sk_A_type, type, sk_A: $i).
% 3.31/3.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 3.31/3.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.31/3.56  thf(t9_yellow_0, conjecture,
% 3.31/3.56    (![A:$i]:
% 3.31/3.56     ( ( l1_orders_2 @ A ) =>
% 3.31/3.56       ( ![B:$i,C:$i]:
% 3.31/3.56         ( ( r1_tarski @ B @ C ) =>
% 3.31/3.56           ( ![D:$i]:
% 3.31/3.56             ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 3.31/3.56               ( ( ( r1_lattice3 @ A @ C @ D ) => ( r1_lattice3 @ A @ B @ D ) ) & 
% 3.31/3.56                 ( ( r2_lattice3 @ A @ C @ D ) => ( r2_lattice3 @ A @ B @ D ) ) ) ) ) ) ) ))).
% 3.31/3.56  thf(zf_stmt_0, negated_conjecture,
% 3.31/3.56    (~( ![A:$i]:
% 3.31/3.56        ( ( l1_orders_2 @ A ) =>
% 3.31/3.56          ( ![B:$i,C:$i]:
% 3.31/3.56            ( ( r1_tarski @ B @ C ) =>
% 3.31/3.56              ( ![D:$i]:
% 3.31/3.56                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 3.31/3.56                  ( ( ( r1_lattice3 @ A @ C @ D ) =>
% 3.31/3.56                      ( r1_lattice3 @ A @ B @ D ) ) & 
% 3.31/3.56                    ( ( r2_lattice3 @ A @ C @ D ) =>
% 3.31/3.56                      ( r2_lattice3 @ A @ B @ D ) ) ) ) ) ) ) ) )),
% 3.31/3.56    inference('cnf.neg', [status(esa)], [t9_yellow_0])).
% 3.31/3.56  thf('0', plain,
% 3.31/3.56      (((r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2)
% 3.31/3.57        | (r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2))),
% 3.31/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.57  thf('1', plain,
% 3.31/3.57      (((r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2)) | 
% 3.31/3.57       ((r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2))),
% 3.31/3.57      inference('split', [status(esa)], ['0'])).
% 3.31/3.57  thf(d1_xboole_0, axiom,
% 3.31/3.57    (![A:$i]:
% 3.31/3.57     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 3.31/3.57  thf('2', plain,
% 3.31/3.57      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 3.31/3.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.31/3.57  thf('3', plain,
% 3.31/3.57      ((~ (r1_lattice3 @ sk_A @ sk_B_1 @ sk_D_2)
% 3.31/3.57        | (r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2))),
% 3.31/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.57  thf('4', plain,
% 3.31/3.57      (((r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2))
% 3.31/3.57         <= (((r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2)))),
% 3.31/3.57      inference('split', [status(esa)], ['3'])).
% 3.31/3.57  thf('5', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 3.31/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.57  thf(d9_lattice3, axiom,
% 3.31/3.57    (![A:$i]:
% 3.31/3.57     ( ( l1_orders_2 @ A ) =>
% 3.31/3.57       ( ![B:$i,C:$i]:
% 3.31/3.57         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 3.31/3.57           ( ( r2_lattice3 @ A @ B @ C ) <=>
% 3.31/3.57             ( ![D:$i]:
% 3.31/3.57               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 3.31/3.57                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ))).
% 3.31/3.57  thf('6', plain,
% 3.31/3.57      (![X35 : $i, X36 : $i, X37 : $i]:
% 3.31/3.57         (~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X36))
% 3.31/3.57          | (r2_hidden @ (sk_D_1 @ X35 @ X37 @ X36) @ X37)
% 3.31/3.57          | (r2_lattice3 @ X36 @ X37 @ X35)
% 3.31/3.57          | ~ (l1_orders_2 @ X36))),
% 3.31/3.57      inference('cnf', [status(esa)], [d9_lattice3])).
% 3.31/3.57  thf('7', plain,
% 3.31/3.57      (![X0 : $i]:
% 3.31/3.57         (~ (l1_orders_2 @ sk_A)
% 3.31/3.57          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 3.31/3.57          | (r2_hidden @ (sk_D_1 @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 3.31/3.57      inference('sup-', [status(thm)], ['5', '6'])).
% 3.31/3.57  thf('8', plain, ((l1_orders_2 @ sk_A)),
% 3.31/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.57  thf('9', plain,
% 3.31/3.57      (![X0 : $i]:
% 3.31/3.57         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 3.31/3.57          | (r2_hidden @ (sk_D_1 @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 3.31/3.57      inference('demod', [status(thm)], ['7', '8'])).
% 3.31/3.57  thf('10', plain, ((r1_tarski @ sk_B_1 @ sk_C_1)),
% 3.31/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.57  thf(t3_subset, axiom,
% 3.31/3.57    (![A:$i,B:$i]:
% 3.31/3.57     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.31/3.57  thf('11', plain,
% 3.31/3.57      (![X18 : $i, X20 : $i]:
% 3.31/3.57         ((m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X20)) | ~ (r1_tarski @ X18 @ X20))),
% 3.31/3.57      inference('cnf', [status(esa)], [t3_subset])).
% 3.31/3.57  thf('12', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_C_1))),
% 3.31/3.57      inference('sup-', [status(thm)], ['10', '11'])).
% 3.31/3.57  thf(t4_subset, axiom,
% 3.31/3.57    (![A:$i,B:$i,C:$i]:
% 3.31/3.57     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 3.31/3.57       ( m1_subset_1 @ A @ C ) ))).
% 3.31/3.57  thf('13', plain,
% 3.31/3.57      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.31/3.57         (~ (r2_hidden @ X21 @ X22)
% 3.31/3.57          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 3.31/3.57          | (m1_subset_1 @ X21 @ X23))),
% 3.31/3.57      inference('cnf', [status(esa)], [t4_subset])).
% 3.31/3.57  thf('14', plain,
% 3.31/3.57      (![X0 : $i]: ((m1_subset_1 @ X0 @ sk_C_1) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 3.31/3.57      inference('sup-', [status(thm)], ['12', '13'])).
% 3.31/3.57  thf('15', plain,
% 3.31/3.57      (((r2_lattice3 @ sk_A @ sk_B_1 @ sk_D_2)
% 3.31/3.57        | (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_B_1 @ sk_A) @ sk_C_1))),
% 3.31/3.57      inference('sup-', [status(thm)], ['9', '14'])).
% 3.31/3.57  thf(t2_subset, axiom,
% 3.31/3.57    (![A:$i,B:$i]:
% 3.31/3.57     ( ( m1_subset_1 @ A @ B ) =>
% 3.31/3.57       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 3.31/3.57  thf('16', plain,
% 3.31/3.57      (![X16 : $i, X17 : $i]:
% 3.31/3.57         ((r2_hidden @ X16 @ X17)
% 3.31/3.57          | (v1_xboole_0 @ X17)
% 3.31/3.57          | ~ (m1_subset_1 @ X16 @ X17))),
% 3.31/3.57      inference('cnf', [status(esa)], [t2_subset])).
% 3.31/3.57  thf('17', plain,
% 3.31/3.57      (((r2_lattice3 @ sk_A @ sk_B_1 @ sk_D_2)
% 3.31/3.57        | (v1_xboole_0 @ sk_C_1)
% 3.31/3.57        | (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B_1 @ sk_A) @ sk_C_1))),
% 3.31/3.57      inference('sup-', [status(thm)], ['15', '16'])).
% 3.31/3.57  thf('18', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 3.31/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.57  thf('19', plain,
% 3.31/3.57      (![X35 : $i, X36 : $i, X37 : $i]:
% 3.31/3.57         (~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X36))
% 3.31/3.57          | (m1_subset_1 @ (sk_D_1 @ X35 @ X37 @ X36) @ (u1_struct_0 @ X36))
% 3.31/3.57          | (r2_lattice3 @ X36 @ X37 @ X35)
% 3.31/3.57          | ~ (l1_orders_2 @ X36))),
% 3.31/3.57      inference('cnf', [status(esa)], [d9_lattice3])).
% 3.31/3.57  thf('20', plain,
% 3.31/3.57      (![X0 : $i]:
% 3.31/3.57         (~ (l1_orders_2 @ sk_A)
% 3.31/3.57          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 3.31/3.57          | (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 3.31/3.57      inference('sup-', [status(thm)], ['18', '19'])).
% 3.31/3.57  thf('21', plain, ((l1_orders_2 @ sk_A)),
% 3.31/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.57  thf('22', plain,
% 3.31/3.57      (![X0 : $i]:
% 3.31/3.57         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 3.31/3.57          | (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 3.31/3.57      inference('demod', [status(thm)], ['20', '21'])).
% 3.31/3.57  thf('23', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 3.31/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.57  thf('24', plain,
% 3.31/3.57      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 3.31/3.57         (~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X36))
% 3.31/3.57          | ~ (r2_lattice3 @ X36 @ X37 @ X35)
% 3.31/3.57          | ~ (r2_hidden @ X38 @ X37)
% 3.31/3.57          | (r1_orders_2 @ X36 @ X38 @ X35)
% 3.31/3.57          | ~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X36))
% 3.31/3.57          | ~ (l1_orders_2 @ X36))),
% 3.31/3.57      inference('cnf', [status(esa)], [d9_lattice3])).
% 3.31/3.57  thf('25', plain,
% 3.31/3.57      (![X0 : $i, X1 : $i]:
% 3.31/3.57         (~ (l1_orders_2 @ sk_A)
% 3.31/3.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.31/3.57          | (r1_orders_2 @ sk_A @ X0 @ sk_D_2)
% 3.31/3.57          | ~ (r2_hidden @ X0 @ X1)
% 3.31/3.57          | ~ (r2_lattice3 @ sk_A @ X1 @ sk_D_2))),
% 3.31/3.57      inference('sup-', [status(thm)], ['23', '24'])).
% 3.31/3.57  thf('26', plain, ((l1_orders_2 @ sk_A)),
% 3.31/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.57  thf('27', plain,
% 3.31/3.57      (![X0 : $i, X1 : $i]:
% 3.31/3.57         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.31/3.57          | (r1_orders_2 @ sk_A @ X0 @ sk_D_2)
% 3.31/3.57          | ~ (r2_hidden @ X0 @ X1)
% 3.31/3.57          | ~ (r2_lattice3 @ sk_A @ X1 @ sk_D_2))),
% 3.31/3.57      inference('demod', [status(thm)], ['25', '26'])).
% 3.31/3.57  thf('28', plain,
% 3.31/3.57      (![X0 : $i, X1 : $i]:
% 3.31/3.57         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 3.31/3.57          | ~ (r2_lattice3 @ sk_A @ X1 @ sk_D_2)
% 3.31/3.57          | ~ (r2_hidden @ (sk_D_1 @ sk_D_2 @ X0 @ sk_A) @ X1)
% 3.31/3.57          | (r1_orders_2 @ sk_A @ (sk_D_1 @ sk_D_2 @ X0 @ sk_A) @ sk_D_2))),
% 3.31/3.57      inference('sup-', [status(thm)], ['22', '27'])).
% 3.31/3.57  thf('29', plain,
% 3.31/3.57      (((v1_xboole_0 @ sk_C_1)
% 3.31/3.57        | (r2_lattice3 @ sk_A @ sk_B_1 @ sk_D_2)
% 3.31/3.57        | (r1_orders_2 @ sk_A @ (sk_D_1 @ sk_D_2 @ sk_B_1 @ sk_A) @ sk_D_2)
% 3.31/3.57        | ~ (r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2)
% 3.31/3.57        | (r2_lattice3 @ sk_A @ sk_B_1 @ sk_D_2))),
% 3.31/3.57      inference('sup-', [status(thm)], ['17', '28'])).
% 3.31/3.57  thf('30', plain,
% 3.31/3.57      ((~ (r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2)
% 3.31/3.57        | (r1_orders_2 @ sk_A @ (sk_D_1 @ sk_D_2 @ sk_B_1 @ sk_A) @ sk_D_2)
% 3.31/3.57        | (r2_lattice3 @ sk_A @ sk_B_1 @ sk_D_2)
% 3.31/3.57        | (v1_xboole_0 @ sk_C_1))),
% 3.31/3.57      inference('simplify', [status(thm)], ['29'])).
% 3.31/3.57  thf('31', plain,
% 3.31/3.57      ((((v1_xboole_0 @ sk_C_1)
% 3.31/3.57         | (r2_lattice3 @ sk_A @ sk_B_1 @ sk_D_2)
% 3.31/3.57         | (r1_orders_2 @ sk_A @ (sk_D_1 @ sk_D_2 @ sk_B_1 @ sk_A) @ sk_D_2)))
% 3.31/3.57         <= (((r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2)))),
% 3.31/3.57      inference('sup-', [status(thm)], ['4', '30'])).
% 3.31/3.57  thf('32', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 3.31/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.57  thf('33', plain,
% 3.31/3.57      (![X35 : $i, X36 : $i, X37 : $i]:
% 3.31/3.57         (~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X36))
% 3.31/3.57          | ~ (r1_orders_2 @ X36 @ (sk_D_1 @ X35 @ X37 @ X36) @ X35)
% 3.31/3.57          | (r2_lattice3 @ X36 @ X37 @ X35)
% 3.31/3.57          | ~ (l1_orders_2 @ X36))),
% 3.31/3.57      inference('cnf', [status(esa)], [d9_lattice3])).
% 3.31/3.57  thf('34', plain,
% 3.31/3.57      (![X0 : $i]:
% 3.31/3.57         (~ (l1_orders_2 @ sk_A)
% 3.31/3.57          | (r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 3.31/3.57          | ~ (r1_orders_2 @ sk_A @ (sk_D_1 @ sk_D_2 @ X0 @ sk_A) @ sk_D_2))),
% 3.31/3.57      inference('sup-', [status(thm)], ['32', '33'])).
% 3.31/3.57  thf('35', plain, ((l1_orders_2 @ sk_A)),
% 3.31/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.57  thf('36', plain,
% 3.31/3.57      (![X0 : $i]:
% 3.31/3.57         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 3.31/3.57          | ~ (r1_orders_2 @ sk_A @ (sk_D_1 @ sk_D_2 @ X0 @ sk_A) @ sk_D_2))),
% 3.31/3.57      inference('demod', [status(thm)], ['34', '35'])).
% 3.31/3.57  thf('37', plain,
% 3.31/3.57      ((((r2_lattice3 @ sk_A @ sk_B_1 @ sk_D_2) | (v1_xboole_0 @ sk_C_1)))
% 3.31/3.57         <= (((r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2)))),
% 3.31/3.57      inference('clc', [status(thm)], ['31', '36'])).
% 3.31/3.57  thf('38', plain,
% 3.31/3.57      ((~ (r1_lattice3 @ sk_A @ sk_B_1 @ sk_D_2)
% 3.31/3.57        | ~ (r2_lattice3 @ sk_A @ sk_B_1 @ sk_D_2))),
% 3.31/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.57  thf('39', plain,
% 3.31/3.57      ((~ (r2_lattice3 @ sk_A @ sk_B_1 @ sk_D_2))
% 3.31/3.57         <= (~ ((r2_lattice3 @ sk_A @ sk_B_1 @ sk_D_2)))),
% 3.31/3.57      inference('split', [status(esa)], ['38'])).
% 3.31/3.57  thf('40', plain,
% 3.31/3.57      (((v1_xboole_0 @ sk_C_1))
% 3.31/3.57         <= (~ ((r2_lattice3 @ sk_A @ sk_B_1 @ sk_D_2)) & 
% 3.31/3.57             ((r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2)))),
% 3.31/3.57      inference('sup-', [status(thm)], ['37', '39'])).
% 3.31/3.57  thf('41', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_C_1))),
% 3.31/3.57      inference('sup-', [status(thm)], ['10', '11'])).
% 3.31/3.57  thf(t5_subset, axiom,
% 3.31/3.57    (![A:$i,B:$i,C:$i]:
% 3.31/3.57     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 3.31/3.57          ( v1_xboole_0 @ C ) ) ))).
% 3.31/3.57  thf('42', plain,
% 3.31/3.57      (![X24 : $i, X25 : $i, X26 : $i]:
% 3.31/3.57         (~ (r2_hidden @ X24 @ X25)
% 3.31/3.57          | ~ (v1_xboole_0 @ X26)
% 3.31/3.57          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26)))),
% 3.31/3.57      inference('cnf', [status(esa)], [t5_subset])).
% 3.31/3.57  thf('43', plain,
% 3.31/3.57      (![X0 : $i]: (~ (v1_xboole_0 @ sk_C_1) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 3.31/3.57      inference('sup-', [status(thm)], ['41', '42'])).
% 3.31/3.57  thf('44', plain,
% 3.31/3.57      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B_1))
% 3.31/3.57         <= (~ ((r2_lattice3 @ sk_A @ sk_B_1 @ sk_D_2)) & 
% 3.31/3.57             ((r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2)))),
% 3.31/3.57      inference('sup-', [status(thm)], ['40', '43'])).
% 3.31/3.57  thf('45', plain,
% 3.31/3.57      (((v1_xboole_0 @ sk_B_1))
% 3.31/3.57         <= (~ ((r2_lattice3 @ sk_A @ sk_B_1 @ sk_D_2)) & 
% 3.31/3.57             ((r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2)))),
% 3.31/3.57      inference('sup-', [status(thm)], ['2', '44'])).
% 3.31/3.57  thf('46', plain,
% 3.31/3.57      (![X0 : $i]:
% 3.31/3.57         ((r2_lattice3 @ sk_A @ X0 @ sk_D_2)
% 3.31/3.57          | (r2_hidden @ (sk_D_1 @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 3.31/3.57      inference('demod', [status(thm)], ['7', '8'])).
% 3.31/3.57  thf('47', plain,
% 3.31/3.57      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.31/3.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.31/3.57  thf('48', plain,
% 3.31/3.57      (![X0 : $i]: ((r2_lattice3 @ sk_A @ X0 @ sk_D_2) | ~ (v1_xboole_0 @ X0))),
% 3.31/3.57      inference('sup-', [status(thm)], ['46', '47'])).
% 3.31/3.57  thf('49', plain,
% 3.31/3.57      ((~ (r2_lattice3 @ sk_A @ sk_B_1 @ sk_D_2))
% 3.31/3.57         <= (~ ((r2_lattice3 @ sk_A @ sk_B_1 @ sk_D_2)))),
% 3.31/3.57      inference('split', [status(esa)], ['38'])).
% 3.31/3.57  thf('50', plain,
% 3.31/3.57      ((~ (v1_xboole_0 @ sk_B_1))
% 3.31/3.57         <= (~ ((r2_lattice3 @ sk_A @ sk_B_1 @ sk_D_2)))),
% 3.31/3.57      inference('sup-', [status(thm)], ['48', '49'])).
% 3.31/3.57  thf('51', plain,
% 3.31/3.57      (($false)
% 3.31/3.57         <= (~ ((r2_lattice3 @ sk_A @ sk_B_1 @ sk_D_2)) & 
% 3.31/3.57             ((r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2)))),
% 3.31/3.57      inference('sup-', [status(thm)], ['45', '50'])).
% 3.31/3.57  thf('52', plain,
% 3.31/3.57      (~ ((r2_lattice3 @ sk_A @ sk_B_1 @ sk_D_2)) | 
% 3.31/3.57       ~ ((r1_lattice3 @ sk_A @ sk_B_1 @ sk_D_2))),
% 3.31/3.57      inference('split', [status(esa)], ['38'])).
% 3.31/3.57  thf('53', plain,
% 3.31/3.57      (((r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2)
% 3.31/3.57        | ~ (r2_lattice3 @ sk_A @ sk_B_1 @ sk_D_2))),
% 3.31/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.57  thf('54', plain,
% 3.31/3.57      (((r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2)) | 
% 3.31/3.57       ~ ((r2_lattice3 @ sk_A @ sk_B_1 @ sk_D_2))),
% 3.31/3.57      inference('split', [status(esa)], ['53'])).
% 3.31/3.57  thf('55', plain,
% 3.31/3.57      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 3.31/3.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.31/3.57  thf('56', plain,
% 3.31/3.57      (((r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2))
% 3.31/3.57         <= (((r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2)))),
% 3.31/3.57      inference('split', [status(esa)], ['53'])).
% 3.31/3.57  thf('57', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 3.31/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.57  thf(d8_lattice3, axiom,
% 3.31/3.57    (![A:$i]:
% 3.31/3.57     ( ( l1_orders_2 @ A ) =>
% 3.31/3.57       ( ![B:$i,C:$i]:
% 3.31/3.57         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 3.31/3.57           ( ( r1_lattice3 @ A @ B @ C ) <=>
% 3.31/3.57             ( ![D:$i]:
% 3.31/3.57               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 3.31/3.57                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ))).
% 3.31/3.57  thf('58', plain,
% 3.31/3.57      (![X31 : $i, X32 : $i, X33 : $i]:
% 3.31/3.57         (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X32))
% 3.31/3.57          | (r2_hidden @ (sk_D @ X31 @ X33 @ X32) @ X33)
% 3.31/3.57          | (r1_lattice3 @ X32 @ X33 @ X31)
% 3.31/3.57          | ~ (l1_orders_2 @ X32))),
% 3.31/3.57      inference('cnf', [status(esa)], [d8_lattice3])).
% 3.31/3.57  thf('59', plain,
% 3.31/3.57      (![X0 : $i]:
% 3.31/3.57         (~ (l1_orders_2 @ sk_A)
% 3.31/3.57          | (r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 3.31/3.57          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 3.31/3.57      inference('sup-', [status(thm)], ['57', '58'])).
% 3.31/3.57  thf('60', plain, ((l1_orders_2 @ sk_A)),
% 3.31/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.57  thf('61', plain,
% 3.31/3.57      (![X0 : $i]:
% 3.31/3.57         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 3.31/3.57          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 3.31/3.57      inference('demod', [status(thm)], ['59', '60'])).
% 3.31/3.57  thf('62', plain,
% 3.31/3.57      (![X0 : $i]: ((m1_subset_1 @ X0 @ sk_C_1) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 3.31/3.57      inference('sup-', [status(thm)], ['12', '13'])).
% 3.31/3.57  thf('63', plain,
% 3.31/3.57      (((r1_lattice3 @ sk_A @ sk_B_1 @ sk_D_2)
% 3.31/3.57        | (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_B_1 @ sk_A) @ sk_C_1))),
% 3.31/3.57      inference('sup-', [status(thm)], ['61', '62'])).
% 3.31/3.57  thf('64', plain,
% 3.31/3.57      (![X16 : $i, X17 : $i]:
% 3.31/3.57         ((r2_hidden @ X16 @ X17)
% 3.31/3.57          | (v1_xboole_0 @ X17)
% 3.31/3.57          | ~ (m1_subset_1 @ X16 @ X17))),
% 3.31/3.57      inference('cnf', [status(esa)], [t2_subset])).
% 3.31/3.57  thf('65', plain,
% 3.31/3.57      (((r1_lattice3 @ sk_A @ sk_B_1 @ sk_D_2)
% 3.31/3.57        | (v1_xboole_0 @ sk_C_1)
% 3.31/3.57        | (r2_hidden @ (sk_D @ sk_D_2 @ sk_B_1 @ sk_A) @ sk_C_1))),
% 3.31/3.57      inference('sup-', [status(thm)], ['63', '64'])).
% 3.31/3.57  thf('66', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 3.31/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.57  thf('67', plain,
% 3.31/3.57      (![X31 : $i, X32 : $i, X33 : $i]:
% 3.31/3.57         (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X32))
% 3.31/3.57          | (m1_subset_1 @ (sk_D @ X31 @ X33 @ X32) @ (u1_struct_0 @ X32))
% 3.31/3.57          | (r1_lattice3 @ X32 @ X33 @ X31)
% 3.31/3.57          | ~ (l1_orders_2 @ X32))),
% 3.31/3.57      inference('cnf', [status(esa)], [d8_lattice3])).
% 3.31/3.57  thf('68', plain,
% 3.31/3.57      (![X0 : $i]:
% 3.31/3.57         (~ (l1_orders_2 @ sk_A)
% 3.31/3.57          | (r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 3.31/3.57          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 3.31/3.57      inference('sup-', [status(thm)], ['66', '67'])).
% 3.31/3.57  thf('69', plain, ((l1_orders_2 @ sk_A)),
% 3.31/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.57  thf('70', plain,
% 3.31/3.57      (![X0 : $i]:
% 3.31/3.57         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 3.31/3.57          | (m1_subset_1 @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 3.31/3.57      inference('demod', [status(thm)], ['68', '69'])).
% 3.31/3.57  thf('71', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 3.31/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.57  thf('72', plain,
% 3.31/3.57      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 3.31/3.57         (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X32))
% 3.31/3.57          | ~ (r1_lattice3 @ X32 @ X33 @ X31)
% 3.31/3.57          | ~ (r2_hidden @ X34 @ X33)
% 3.31/3.57          | (r1_orders_2 @ X32 @ X31 @ X34)
% 3.31/3.57          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X32))
% 3.31/3.57          | ~ (l1_orders_2 @ X32))),
% 3.31/3.57      inference('cnf', [status(esa)], [d8_lattice3])).
% 3.31/3.57  thf('73', plain,
% 3.31/3.57      (![X0 : $i, X1 : $i]:
% 3.31/3.57         (~ (l1_orders_2 @ sk_A)
% 3.31/3.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.31/3.57          | (r1_orders_2 @ sk_A @ sk_D_2 @ X0)
% 3.31/3.57          | ~ (r2_hidden @ X0 @ X1)
% 3.31/3.57          | ~ (r1_lattice3 @ sk_A @ X1 @ sk_D_2))),
% 3.31/3.57      inference('sup-', [status(thm)], ['71', '72'])).
% 3.31/3.57  thf('74', plain, ((l1_orders_2 @ sk_A)),
% 3.31/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.57  thf('75', plain,
% 3.31/3.57      (![X0 : $i, X1 : $i]:
% 3.31/3.57         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.31/3.57          | (r1_orders_2 @ sk_A @ sk_D_2 @ X0)
% 3.31/3.57          | ~ (r2_hidden @ X0 @ X1)
% 3.31/3.57          | ~ (r1_lattice3 @ sk_A @ X1 @ sk_D_2))),
% 3.31/3.57      inference('demod', [status(thm)], ['73', '74'])).
% 3.31/3.57  thf('76', plain,
% 3.31/3.57      (![X0 : $i, X1 : $i]:
% 3.31/3.57         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 3.31/3.57          | ~ (r1_lattice3 @ sk_A @ X1 @ sk_D_2)
% 3.31/3.57          | ~ (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X1)
% 3.31/3.57          | (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 3.31/3.57      inference('sup-', [status(thm)], ['70', '75'])).
% 3.31/3.57  thf('77', plain,
% 3.31/3.57      (((v1_xboole_0 @ sk_C_1)
% 3.31/3.57        | (r1_lattice3 @ sk_A @ sk_B_1 @ sk_D_2)
% 3.31/3.57        | (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_B_1 @ sk_A))
% 3.31/3.57        | ~ (r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2)
% 3.31/3.57        | (r1_lattice3 @ sk_A @ sk_B_1 @ sk_D_2))),
% 3.31/3.57      inference('sup-', [status(thm)], ['65', '76'])).
% 3.31/3.57  thf('78', plain,
% 3.31/3.57      ((~ (r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2)
% 3.31/3.57        | (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_B_1 @ sk_A))
% 3.31/3.57        | (r1_lattice3 @ sk_A @ sk_B_1 @ sk_D_2)
% 3.31/3.57        | (v1_xboole_0 @ sk_C_1))),
% 3.31/3.57      inference('simplify', [status(thm)], ['77'])).
% 3.31/3.57  thf('79', plain,
% 3.31/3.57      ((((v1_xboole_0 @ sk_C_1)
% 3.31/3.57         | (r1_lattice3 @ sk_A @ sk_B_1 @ sk_D_2)
% 3.31/3.57         | (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_B_1 @ sk_A))))
% 3.31/3.57         <= (((r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2)))),
% 3.31/3.57      inference('sup-', [status(thm)], ['56', '78'])).
% 3.31/3.57  thf('80', plain, ((m1_subset_1 @ sk_D_2 @ (u1_struct_0 @ sk_A))),
% 3.31/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.57  thf('81', plain,
% 3.31/3.57      (![X31 : $i, X32 : $i, X33 : $i]:
% 3.31/3.57         (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X32))
% 3.31/3.57          | ~ (r1_orders_2 @ X32 @ X31 @ (sk_D @ X31 @ X33 @ X32))
% 3.31/3.57          | (r1_lattice3 @ X32 @ X33 @ X31)
% 3.31/3.57          | ~ (l1_orders_2 @ X32))),
% 3.31/3.57      inference('cnf', [status(esa)], [d8_lattice3])).
% 3.31/3.57  thf('82', plain,
% 3.31/3.57      (![X0 : $i]:
% 3.31/3.57         (~ (l1_orders_2 @ sk_A)
% 3.31/3.57          | (r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 3.31/3.57          | ~ (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 3.31/3.57      inference('sup-', [status(thm)], ['80', '81'])).
% 3.31/3.57  thf('83', plain, ((l1_orders_2 @ sk_A)),
% 3.31/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.31/3.57  thf('84', plain,
% 3.31/3.57      (![X0 : $i]:
% 3.31/3.57         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 3.31/3.57          | ~ (r1_orders_2 @ sk_A @ sk_D_2 @ (sk_D @ sk_D_2 @ X0 @ sk_A)))),
% 3.31/3.57      inference('demod', [status(thm)], ['82', '83'])).
% 3.31/3.57  thf('85', plain,
% 3.31/3.57      ((((r1_lattice3 @ sk_A @ sk_B_1 @ sk_D_2) | (v1_xboole_0 @ sk_C_1)))
% 3.31/3.57         <= (((r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2)))),
% 3.31/3.57      inference('clc', [status(thm)], ['79', '84'])).
% 3.31/3.57  thf('86', plain,
% 3.31/3.57      ((~ (r1_lattice3 @ sk_A @ sk_B_1 @ sk_D_2))
% 3.31/3.57         <= (~ ((r1_lattice3 @ sk_A @ sk_B_1 @ sk_D_2)))),
% 3.31/3.57      inference('split', [status(esa)], ['38'])).
% 3.31/3.57  thf('87', plain,
% 3.31/3.57      (((v1_xboole_0 @ sk_C_1))
% 3.31/3.57         <= (~ ((r1_lattice3 @ sk_A @ sk_B_1 @ sk_D_2)) & 
% 3.31/3.57             ((r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2)))),
% 3.31/3.57      inference('sup-', [status(thm)], ['85', '86'])).
% 3.31/3.57  thf('88', plain,
% 3.31/3.57      (![X0 : $i]: (~ (v1_xboole_0 @ sk_C_1) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 3.31/3.57      inference('sup-', [status(thm)], ['41', '42'])).
% 3.31/3.57  thf('89', plain,
% 3.31/3.57      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B_1))
% 3.31/3.57         <= (~ ((r1_lattice3 @ sk_A @ sk_B_1 @ sk_D_2)) & 
% 3.31/3.57             ((r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2)))),
% 3.31/3.57      inference('sup-', [status(thm)], ['87', '88'])).
% 3.31/3.57  thf('90', plain,
% 3.31/3.57      (((v1_xboole_0 @ sk_B_1))
% 3.31/3.57         <= (~ ((r1_lattice3 @ sk_A @ sk_B_1 @ sk_D_2)) & 
% 3.31/3.57             ((r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2)))),
% 3.31/3.57      inference('sup-', [status(thm)], ['55', '89'])).
% 3.31/3.57  thf('91', plain,
% 3.31/3.57      (![X0 : $i]:
% 3.31/3.57         ((r1_lattice3 @ sk_A @ X0 @ sk_D_2)
% 3.31/3.57          | (r2_hidden @ (sk_D @ sk_D_2 @ X0 @ sk_A) @ X0))),
% 3.31/3.57      inference('demod', [status(thm)], ['59', '60'])).
% 3.31/3.57  thf('92', plain,
% 3.31/3.57      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.31/3.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.31/3.57  thf('93', plain,
% 3.31/3.57      (![X0 : $i]: ((r1_lattice3 @ sk_A @ X0 @ sk_D_2) | ~ (v1_xboole_0 @ X0))),
% 3.31/3.57      inference('sup-', [status(thm)], ['91', '92'])).
% 3.31/3.57  thf('94', plain,
% 3.31/3.57      ((~ (r1_lattice3 @ sk_A @ sk_B_1 @ sk_D_2))
% 3.31/3.57         <= (~ ((r1_lattice3 @ sk_A @ sk_B_1 @ sk_D_2)))),
% 3.31/3.57      inference('split', [status(esa)], ['38'])).
% 3.31/3.57  thf('95', plain,
% 3.31/3.57      ((~ (v1_xboole_0 @ sk_B_1))
% 3.31/3.57         <= (~ ((r1_lattice3 @ sk_A @ sk_B_1 @ sk_D_2)))),
% 3.31/3.57      inference('sup-', [status(thm)], ['93', '94'])).
% 3.31/3.57  thf('96', plain,
% 3.31/3.57      (((r1_lattice3 @ sk_A @ sk_B_1 @ sk_D_2)) | 
% 3.31/3.57       ~ ((r1_lattice3 @ sk_A @ sk_C_1 @ sk_D_2))),
% 3.31/3.57      inference('sup-', [status(thm)], ['90', '95'])).
% 3.31/3.57  thf('97', plain, (~ ((r2_lattice3 @ sk_A @ sk_B_1 @ sk_D_2))),
% 3.31/3.57      inference('sat_resolution*', [status(thm)], ['52', '54', '96'])).
% 3.31/3.57  thf('98', plain, (~ ((r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2))),
% 3.31/3.57      inference('simpl_trail', [status(thm)], ['51', '97'])).
% 3.31/3.57  thf('99', plain,
% 3.31/3.57      (~ ((r1_lattice3 @ sk_A @ sk_B_1 @ sk_D_2)) | 
% 3.31/3.57       ((r2_lattice3 @ sk_A @ sk_C_1 @ sk_D_2))),
% 3.31/3.57      inference('split', [status(esa)], ['3'])).
% 3.31/3.57  thf('100', plain, ($false),
% 3.31/3.57      inference('sat_resolution*', [status(thm)], ['1', '98', '99', '96'])).
% 3.31/3.57  
% 3.31/3.57  % SZS output end Refutation
% 3.31/3.57  
% 3.31/3.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
