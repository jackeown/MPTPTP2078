%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PSWV3y0TWN

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:23 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 382 expanded)
%              Number of leaves         :   36 ( 130 expanded)
%              Depth                    :   17
%              Number of atoms          : 1063 (5095 expanded)
%              Number of equality atoms :   36 ( 204 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r2_wellord1_type,type,(
    r2_wellord1: $i > $i > $o )).

thf(k1_orders_2_type,type,(
    k1_orders_2: $i > $i > $i )).

thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_orders_2_type,type,(
    k4_orders_2: $i > $i > $i )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(t87_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) )
           != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) )
             != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t87_orders_2])).

thf('0',plain,(
    m1_orders_1 @ sk_B_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_orders_1 @ sk_B_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(existence_m2_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) )
     => ? [C: $i] :
          ( m2_orders_2 @ C @ A @ B ) ) )).

thf('2',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_orders_2 @ X29 )
      | ~ ( v5_orders_2 @ X29 )
      | ~ ( v4_orders_2 @ X29 )
      | ~ ( v3_orders_2 @ X29 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_orders_1 @ X30 @ ( k1_orders_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( m2_orders_2 @ ( sk_C_1 @ X30 @ X29 ) @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[existence_m2_orders_2])).

thf('3',plain,
    ( ( m2_orders_2 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( m2_orders_2 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4','5','6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m2_orders_2 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_orders_1 @ sk_B_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m2_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) )
     => ! [C: $i] :
          ( ( m2_orders_2 @ C @ A @ B )
         => ( ( v6_orders_2 @ C @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( l1_orders_2 @ X26 )
      | ~ ( v5_orders_2 @ X26 )
      | ~ ( v4_orders_2 @ X26 )
      | ~ ( v3_orders_2 @ X26 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_orders_1 @ X27 @ ( k1_orders_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( m2_orders_2 @ X28 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_orders_2])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf('19',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','20'])).

thf('22',plain,(
    m2_orders_2 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 ),
    inference(clc,[status(thm)],['8','9'])).

thf('23',plain,(
    m1_orders_1 @ sk_B_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d17_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( C
                = ( k4_orders_2 @ A @ B ) )
            <=> ! [D: $i] :
                  ( ( r2_hidden @ D @ C )
                <=> ( m2_orders_2 @ D @ A @ B ) ) ) ) ) )).

thf('24',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_orders_1 @ X20 @ ( k1_orders_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( X22
       != ( k4_orders_2 @ X21 @ X20 ) )
      | ( r2_hidden @ X23 @ X22 )
      | ~ ( m2_orders_2 @ X23 @ X21 @ X20 )
      | ~ ( l1_orders_2 @ X21 )
      | ~ ( v5_orders_2 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v3_orders_2 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d17_orders_2])).

thf('25',plain,(
    ! [X20: $i,X21: $i,X23: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v3_orders_2 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v5_orders_2 @ X21 )
      | ~ ( l1_orders_2 @ X21 )
      | ~ ( m2_orders_2 @ X23 @ X21 @ X20 )
      | ( r2_hidden @ X23 @ ( k4_orders_2 @ X21 @ X20 ) )
      | ~ ( m1_orders_1 @ X20 @ ( k1_orders_1 @ ( u1_struct_0 @ X21 ) ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27','28','29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['22','33'])).

thf(t6_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i,G: $i] :
                  ( ( ( r2_hidden @ C @ D )
                    & ( r2_hidden @ D @ E )
                    & ( r2_hidden @ E @ F )
                    & ( r2_hidden @ F @ G )
                    & ( r2_hidden @ G @ B ) )
                 => ( r1_xboole_0 @ C @ A ) ) ) ) )).

thf('35',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('36',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r2_hidden @ X3 @ X1 )
      | ( r2_hidden @ X3 @ X4 )
      | ( X4
       != ( k3_tarski @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('37',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X3 @ ( k3_tarski @ X2 ) )
      | ~ ( r2_hidden @ X3 @ X1 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k3_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,
    ( ( r2_hidden @ ( sk_B @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) @ ( k3_tarski @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) )
    | ( ( sk_C_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','38'])).

thf('40',plain,
    ( ( k3_tarski @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( r2_hidden @ ( sk_B @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) @ k1_xboole_0 )
    | ( ( sk_C_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('42',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('43',plain,
    ( ( ( sk_C_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_tarski @ k1_xboole_0 @ ( sk_B @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('45',plain,
    ( ( sk_C_1 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','45'])).

thf(d16_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( ( v6_orders_2 @ C @ A )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( m2_orders_2 @ C @ A @ B )
              <=> ( ( C != k1_xboole_0 )
                  & ( r2_wellord1 @ ( u1_orders_2 @ A ) @ C )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r2_hidden @ D @ C )
                       => ( ( k1_funct_1 @ B @ ( k1_orders_2 @ A @ ( k3_orders_2 @ A @ C @ D ) ) )
                          = D ) ) ) ) ) ) ) ) )).

thf('47',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_orders_1 @ X16 @ ( k1_orders_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( m2_orders_2 @ X18 @ X17 @ X16 )
      | ( X18 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v6_orders_2 @ X18 @ X17 )
      | ~ ( l1_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v3_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d16_orders_2])).

thf('48',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( v3_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( l1_orders_2 @ X17 )
      | ~ ( v6_orders_2 @ k1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( m2_orders_2 @ k1_xboole_0 @ X17 @ X16 )
      | ~ ( m1_orders_1 @ X16 @ ( k1_orders_1 @ ( u1_struct_0 @ X17 ) ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( m1_orders_1 @ X0 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m2_orders_2 @ k1_xboole_0 @ sk_A @ X0 )
      | ~ ( v6_orders_2 @ k1_xboole_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,
    ( ( k3_tarski @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k3_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( sk_B @ X0 ) ) @ ( k3_tarski @ X0 ) )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k3_tarski @ X0 ) @ ( sk_B @ ( sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( sk_B @ ( sk_B @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ) )
    | ( ( k4_orders_2 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( sk_B @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('58',plain,
    ( ( ( k4_orders_2 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( sk_B @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf('60',plain,
    ( ( r2_hidden @ k1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    | ( ( k4_orders_2 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k4_orders_2 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k4_orders_2 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( r2_hidden @ k1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    m1_orders_1 @ sk_B_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X20: $i,X21: $i,X22: $i,X24: $i] :
      ( ~ ( m1_orders_1 @ X20 @ ( k1_orders_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( X22
       != ( k4_orders_2 @ X21 @ X20 ) )
      | ( m2_orders_2 @ X24 @ X21 @ X20 )
      | ~ ( r2_hidden @ X24 @ X22 )
      | ~ ( l1_orders_2 @ X21 )
      | ~ ( v5_orders_2 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v3_orders_2 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d17_orders_2])).

thf('64',plain,(
    ! [X20: $i,X21: $i,X24: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v3_orders_2 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v5_orders_2 @ X21 )
      | ~ ( l1_orders_2 @ X21 )
      | ~ ( r2_hidden @ X24 @ ( k4_orders_2 @ X21 @ X20 ) )
      | ( m2_orders_2 @ X24 @ X21 @ X20 )
      | ~ ( m1_orders_1 @ X20 @ ( k1_orders_1 @ ( u1_struct_0 @ X21 ) ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','64'])).

thf('66',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66','67','68','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ( k4_orders_2 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['61','72'])).

thf('74',plain,(
    m1_orders_1 @ sk_B_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( l1_orders_2 @ X26 )
      | ~ ( v5_orders_2 @ X26 )
      | ~ ( v4_orders_2 @ X26 )
      | ~ ( v3_orders_2 @ X26 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_orders_1 @ X27 @ ( k1_orders_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( v6_orders_2 @ X28 @ X26 )
      | ~ ( m2_orders_2 @ X28 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_orders_2])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( v6_orders_2 @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( v6_orders_2 @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','77','78','79','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v6_orders_2 @ X0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( k4_orders_2 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( v6_orders_2 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['73','83'])).

thf('85',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['22','33'])).

thf('86',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('87',plain,(
    ~ ( r1_tarski @ ( k4_orders_2 @ sk_A @ sk_B_1 ) @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v6_orders_2 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('90',plain,(
    v6_orders_2 @ k1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( m1_orders_1 @ X0 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m2_orders_2 @ k1_xboole_0 @ sk_A @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','90','91','92','93','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ k1_xboole_0 @ sk_A @ X0 )
      | ~ ( m1_orders_1 @ X0 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    ~ ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','97'])).

thf('99',plain,(
    m2_orders_2 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 ),
    inference(clc,[status(thm)],['8','9'])).

thf('100',plain,
    ( ( sk_C_1 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['43','44'])).

thf('101',plain,(
    m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1 ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    $false ),
    inference(demod,[status(thm)],['98','101'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PSWV3y0TWN
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:26:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.54/0.76  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.54/0.76  % Solved by: fo/fo7.sh
% 0.54/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.76  % done 373 iterations in 0.301s
% 0.54/0.76  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.54/0.76  % SZS output start Refutation
% 0.54/0.76  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.54/0.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.54/0.76  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.54/0.76  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.54/0.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.54/0.76  thf(r2_wellord1_type, type, r2_wellord1: $i > $i > $o).
% 0.54/0.76  thf(k1_orders_2_type, type, k1_orders_2: $i > $i > $i).
% 0.54/0.76  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 0.54/0.76  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.54/0.76  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.54/0.76  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.54/0.76  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.54/0.76  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.54/0.76  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.54/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.76  thf(k4_orders_2_type, type, k4_orders_2: $i > $i > $i).
% 0.54/0.76  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.54/0.76  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.54/0.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.76  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.54/0.76  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.54/0.76  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.54/0.76  thf(sk_B_type, type, sk_B: $i > $i).
% 0.54/0.76  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.54/0.76  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.54/0.76  thf(t87_orders_2, conjecture,
% 0.54/0.76    (![A:$i]:
% 0.54/0.76     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.54/0.76         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.54/0.76       ( ![B:$i]:
% 0.54/0.76         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.76           ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ))).
% 0.54/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.76    (~( ![A:$i]:
% 0.54/0.76        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.54/0.76            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.54/0.76          ( ![B:$i]:
% 0.54/0.76            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.76              ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ) )),
% 0.54/0.76    inference('cnf.neg', [status(esa)], [t87_orders_2])).
% 0.54/0.76  thf('0', plain,
% 0.54/0.76      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('1', plain,
% 0.54/0.76      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf(existence_m2_orders_2, axiom,
% 0.54/0.76    (![A:$i,B:$i]:
% 0.54/0.76     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.54/0.76         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.54/0.76         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.54/0.76       ( ?[C:$i]: ( m2_orders_2 @ C @ A @ B ) ) ))).
% 0.54/0.76  thf('2', plain,
% 0.54/0.76      (![X29 : $i, X30 : $i]:
% 0.54/0.76         (~ (l1_orders_2 @ X29)
% 0.54/0.76          | ~ (v5_orders_2 @ X29)
% 0.54/0.76          | ~ (v4_orders_2 @ X29)
% 0.54/0.76          | ~ (v3_orders_2 @ X29)
% 0.54/0.76          | (v2_struct_0 @ X29)
% 0.54/0.76          | ~ (m1_orders_1 @ X30 @ (k1_orders_1 @ (u1_struct_0 @ X29)))
% 0.54/0.76          | (m2_orders_2 @ (sk_C_1 @ X30 @ X29) @ X29 @ X30))),
% 0.54/0.76      inference('cnf', [status(esa)], [existence_m2_orders_2])).
% 0.54/0.76  thf('3', plain,
% 0.54/0.76      (((m2_orders_2 @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A @ sk_B_1)
% 0.54/0.76        | (v2_struct_0 @ sk_A)
% 0.54/0.76        | ~ (v3_orders_2 @ sk_A)
% 0.54/0.76        | ~ (v4_orders_2 @ sk_A)
% 0.54/0.76        | ~ (v5_orders_2 @ sk_A)
% 0.54/0.76        | ~ (l1_orders_2 @ sk_A))),
% 0.54/0.76      inference('sup-', [status(thm)], ['1', '2'])).
% 0.54/0.76  thf('4', plain, ((v3_orders_2 @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('5', plain, ((v4_orders_2 @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('6', plain, ((v5_orders_2 @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('7', plain, ((l1_orders_2 @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('8', plain,
% 0.54/0.76      (((m2_orders_2 @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A @ sk_B_1)
% 0.54/0.76        | (v2_struct_0 @ sk_A))),
% 0.54/0.76      inference('demod', [status(thm)], ['3', '4', '5', '6', '7'])).
% 0.54/0.76  thf('9', plain, (~ (v2_struct_0 @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('10', plain, ((m2_orders_2 @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A @ sk_B_1)),
% 0.54/0.76      inference('clc', [status(thm)], ['8', '9'])).
% 0.54/0.76  thf('11', plain,
% 0.54/0.76      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf(dt_m2_orders_2, axiom,
% 0.54/0.76    (![A:$i,B:$i]:
% 0.54/0.76     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.54/0.76         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.54/0.76         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.54/0.76       ( ![C:$i]:
% 0.54/0.76         ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.54/0.76           ( ( v6_orders_2 @ C @ A ) & 
% 0.54/0.76             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.54/0.76  thf('12', plain,
% 0.54/0.76      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.54/0.76         (~ (l1_orders_2 @ X26)
% 0.54/0.76          | ~ (v5_orders_2 @ X26)
% 0.54/0.76          | ~ (v4_orders_2 @ X26)
% 0.54/0.76          | ~ (v3_orders_2 @ X26)
% 0.54/0.76          | (v2_struct_0 @ X26)
% 0.54/0.76          | ~ (m1_orders_1 @ X27 @ (k1_orders_1 @ (u1_struct_0 @ X26)))
% 0.54/0.76          | (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.54/0.76          | ~ (m2_orders_2 @ X28 @ X26 @ X27))),
% 0.54/0.76      inference('cnf', [status(esa)], [dt_m2_orders_2])).
% 0.54/0.76  thf('13', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.54/0.76          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.54/0.76          | (v2_struct_0 @ sk_A)
% 0.54/0.76          | ~ (v3_orders_2 @ sk_A)
% 0.54/0.76          | ~ (v4_orders_2 @ sk_A)
% 0.54/0.76          | ~ (v5_orders_2 @ sk_A)
% 0.54/0.76          | ~ (l1_orders_2 @ sk_A))),
% 0.54/0.76      inference('sup-', [status(thm)], ['11', '12'])).
% 0.54/0.76  thf('14', plain, ((v3_orders_2 @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('15', plain, ((v4_orders_2 @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('16', plain, ((v5_orders_2 @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('17', plain, ((l1_orders_2 @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('18', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.54/0.76          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.54/0.76          | (v2_struct_0 @ sk_A))),
% 0.54/0.76      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.54/0.76  thf('19', plain, (~ (v2_struct_0 @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('20', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.54/0.76          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1))),
% 0.54/0.76      inference('clc', [status(thm)], ['18', '19'])).
% 0.54/0.76  thf('21', plain,
% 0.54/0.76      ((m1_subset_1 @ (sk_C_1 @ sk_B_1 @ sk_A) @ 
% 0.54/0.76        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['10', '20'])).
% 0.54/0.76  thf('22', plain, ((m2_orders_2 @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A @ sk_B_1)),
% 0.54/0.76      inference('clc', [status(thm)], ['8', '9'])).
% 0.54/0.76  thf('23', plain,
% 0.54/0.76      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf(d17_orders_2, axiom,
% 0.54/0.76    (![A:$i]:
% 0.54/0.76     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.54/0.76         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.54/0.76       ( ![B:$i]:
% 0.54/0.76         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.76           ( ![C:$i]:
% 0.54/0.76             ( ( ( C ) = ( k4_orders_2 @ A @ B ) ) <=>
% 0.54/0.76               ( ![D:$i]:
% 0.54/0.76                 ( ( r2_hidden @ D @ C ) <=> ( m2_orders_2 @ D @ A @ B ) ) ) ) ) ) ) ))).
% 0.54/0.76  thf('24', plain,
% 0.54/0.76      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.54/0.76         (~ (m1_orders_1 @ X20 @ (k1_orders_1 @ (u1_struct_0 @ X21)))
% 0.54/0.76          | ((X22) != (k4_orders_2 @ X21 @ X20))
% 0.54/0.76          | (r2_hidden @ X23 @ X22)
% 0.54/0.76          | ~ (m2_orders_2 @ X23 @ X21 @ X20)
% 0.54/0.76          | ~ (l1_orders_2 @ X21)
% 0.54/0.76          | ~ (v5_orders_2 @ X21)
% 0.54/0.76          | ~ (v4_orders_2 @ X21)
% 0.54/0.76          | ~ (v3_orders_2 @ X21)
% 0.54/0.76          | (v2_struct_0 @ X21))),
% 0.54/0.76      inference('cnf', [status(esa)], [d17_orders_2])).
% 0.54/0.76  thf('25', plain,
% 0.54/0.76      (![X20 : $i, X21 : $i, X23 : $i]:
% 0.54/0.76         ((v2_struct_0 @ X21)
% 0.54/0.76          | ~ (v3_orders_2 @ X21)
% 0.54/0.76          | ~ (v4_orders_2 @ X21)
% 0.54/0.76          | ~ (v5_orders_2 @ X21)
% 0.54/0.76          | ~ (l1_orders_2 @ X21)
% 0.54/0.76          | ~ (m2_orders_2 @ X23 @ X21 @ X20)
% 0.54/0.76          | (r2_hidden @ X23 @ (k4_orders_2 @ X21 @ X20))
% 0.54/0.76          | ~ (m1_orders_1 @ X20 @ (k1_orders_1 @ (u1_struct_0 @ X21))))),
% 0.54/0.76      inference('simplify', [status(thm)], ['24'])).
% 0.54/0.76  thf('26', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         ((r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.54/0.76          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.54/0.76          | ~ (l1_orders_2 @ sk_A)
% 0.54/0.76          | ~ (v5_orders_2 @ sk_A)
% 0.54/0.76          | ~ (v4_orders_2 @ sk_A)
% 0.54/0.76          | ~ (v3_orders_2 @ sk_A)
% 0.54/0.76          | (v2_struct_0 @ sk_A))),
% 0.54/0.76      inference('sup-', [status(thm)], ['23', '25'])).
% 0.54/0.76  thf('27', plain, ((l1_orders_2 @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('28', plain, ((v5_orders_2 @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('29', plain, ((v4_orders_2 @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('30', plain, ((v3_orders_2 @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('31', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         ((r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.54/0.76          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.54/0.76          | (v2_struct_0 @ sk_A))),
% 0.54/0.76      inference('demod', [status(thm)], ['26', '27', '28', '29', '30'])).
% 0.54/0.76  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('33', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.54/0.76          | (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1)))),
% 0.54/0.76      inference('clc', [status(thm)], ['31', '32'])).
% 0.54/0.76  thf('34', plain,
% 0.54/0.76      ((r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ (k4_orders_2 @ sk_A @ sk_B_1))),
% 0.54/0.76      inference('sup-', [status(thm)], ['22', '33'])).
% 0.54/0.76  thf(t6_mcart_1, axiom,
% 0.54/0.76    (![A:$i]:
% 0.54/0.76     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.54/0.76          ( ![B:$i]:
% 0.54/0.76            ( ~( ( r2_hidden @ B @ A ) & 
% 0.54/0.76                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.54/0.76                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 0.54/0.76                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 0.54/0.76                       ( r2_hidden @ G @ B ) ) =>
% 0.54/0.76                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.54/0.76  thf('35', plain,
% 0.54/0.76      (![X10 : $i]:
% 0.54/0.76         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.54/0.76      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.54/0.76  thf(d4_tarski, axiom,
% 0.54/0.76    (![A:$i,B:$i]:
% 0.54/0.76     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 0.54/0.76       ( ![C:$i]:
% 0.54/0.76         ( ( r2_hidden @ C @ B ) <=>
% 0.54/0.76           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 0.54/0.76  thf('36', plain,
% 0.54/0.76      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.54/0.76         (~ (r2_hidden @ X1 @ X2)
% 0.54/0.76          | ~ (r2_hidden @ X3 @ X1)
% 0.54/0.76          | (r2_hidden @ X3 @ X4)
% 0.54/0.76          | ((X4) != (k3_tarski @ X2)))),
% 0.54/0.76      inference('cnf', [status(esa)], [d4_tarski])).
% 0.54/0.76  thf('37', plain,
% 0.54/0.76      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.54/0.76         ((r2_hidden @ X3 @ (k3_tarski @ X2))
% 0.54/0.76          | ~ (r2_hidden @ X3 @ X1)
% 0.54/0.76          | ~ (r2_hidden @ X1 @ X2))),
% 0.54/0.76      inference('simplify', [status(thm)], ['36'])).
% 0.54/0.76  thf('38', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i]:
% 0.54/0.76         (((X0) = (k1_xboole_0))
% 0.54/0.76          | ~ (r2_hidden @ X0 @ X1)
% 0.54/0.76          | (r2_hidden @ (sk_B @ X0) @ (k3_tarski @ X1)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['35', '37'])).
% 0.54/0.76  thf('39', plain,
% 0.54/0.76      (((r2_hidden @ (sk_B @ (sk_C_1 @ sk_B_1 @ sk_A)) @ 
% 0.54/0.76         (k3_tarski @ (k4_orders_2 @ sk_A @ sk_B_1)))
% 0.54/0.76        | ((sk_C_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['34', '38'])).
% 0.54/0.76  thf('40', plain,
% 0.54/0.76      (((k3_tarski @ (k4_orders_2 @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('41', plain,
% 0.54/0.76      (((r2_hidden @ (sk_B @ (sk_C_1 @ sk_B_1 @ sk_A)) @ k1_xboole_0)
% 0.54/0.76        | ((sk_C_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.54/0.76      inference('demod', [status(thm)], ['39', '40'])).
% 0.54/0.76  thf(t7_ordinal1, axiom,
% 0.54/0.76    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.54/0.76  thf('42', plain,
% 0.54/0.76      (![X8 : $i, X9 : $i]: (~ (r2_hidden @ X8 @ X9) | ~ (r1_tarski @ X9 @ X8))),
% 0.54/0.76      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.54/0.76  thf('43', plain,
% 0.54/0.76      ((((sk_C_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.54/0.76        | ~ (r1_tarski @ k1_xboole_0 @ (sk_B @ (sk_C_1 @ sk_B_1 @ sk_A))))),
% 0.54/0.76      inference('sup-', [status(thm)], ['41', '42'])).
% 0.54/0.76  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.54/0.76  thf('44', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.54/0.76      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.54/0.76  thf('45', plain, (((sk_C_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 0.54/0.76      inference('demod', [status(thm)], ['43', '44'])).
% 0.54/0.76  thf('46', plain,
% 0.54/0.76      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.76      inference('demod', [status(thm)], ['21', '45'])).
% 0.54/0.76  thf(d16_orders_2, axiom,
% 0.54/0.76    (![A:$i]:
% 0.54/0.76     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.54/0.76         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.54/0.76       ( ![B:$i]:
% 0.54/0.76         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.76           ( ![C:$i]:
% 0.54/0.76             ( ( ( v6_orders_2 @ C @ A ) & 
% 0.54/0.76                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.54/0.76               ( ( m2_orders_2 @ C @ A @ B ) <=>
% 0.54/0.76                 ( ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.54/0.76                   ( r2_wellord1 @ ( u1_orders_2 @ A ) @ C ) & 
% 0.54/0.76                   ( ![D:$i]:
% 0.54/0.76                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.54/0.76                       ( ( r2_hidden @ D @ C ) =>
% 0.54/0.76                         ( ( k1_funct_1 @
% 0.54/0.76                             B @ 
% 0.54/0.76                             ( k1_orders_2 @ A @ ( k3_orders_2 @ A @ C @ D ) ) ) =
% 0.54/0.76                           ( D ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.54/0.76  thf('47', plain,
% 0.54/0.76      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.54/0.76         (~ (m1_orders_1 @ X16 @ (k1_orders_1 @ (u1_struct_0 @ X17)))
% 0.54/0.76          | ~ (m2_orders_2 @ X18 @ X17 @ X16)
% 0.54/0.76          | ((X18) != (k1_xboole_0))
% 0.54/0.76          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.54/0.76          | ~ (v6_orders_2 @ X18 @ X17)
% 0.54/0.76          | ~ (l1_orders_2 @ X17)
% 0.54/0.76          | ~ (v5_orders_2 @ X17)
% 0.54/0.76          | ~ (v4_orders_2 @ X17)
% 0.54/0.76          | ~ (v3_orders_2 @ X17)
% 0.54/0.76          | (v2_struct_0 @ X17))),
% 0.54/0.76      inference('cnf', [status(esa)], [d16_orders_2])).
% 0.54/0.76  thf('48', plain,
% 0.54/0.76      (![X16 : $i, X17 : $i]:
% 0.54/0.76         ((v2_struct_0 @ X17)
% 0.54/0.76          | ~ (v3_orders_2 @ X17)
% 0.54/0.76          | ~ (v4_orders_2 @ X17)
% 0.54/0.76          | ~ (v5_orders_2 @ X17)
% 0.54/0.76          | ~ (l1_orders_2 @ X17)
% 0.54/0.76          | ~ (v6_orders_2 @ k1_xboole_0 @ X17)
% 0.54/0.76          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.54/0.76          | ~ (m2_orders_2 @ k1_xboole_0 @ X17 @ X16)
% 0.54/0.76          | ~ (m1_orders_1 @ X16 @ (k1_orders_1 @ (u1_struct_0 @ X17))))),
% 0.54/0.76      inference('simplify', [status(thm)], ['47'])).
% 0.54/0.76  thf('49', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (~ (m1_orders_1 @ X0 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))
% 0.54/0.76          | ~ (m2_orders_2 @ k1_xboole_0 @ sk_A @ X0)
% 0.54/0.76          | ~ (v6_orders_2 @ k1_xboole_0 @ sk_A)
% 0.54/0.76          | ~ (l1_orders_2 @ sk_A)
% 0.54/0.76          | ~ (v5_orders_2 @ sk_A)
% 0.54/0.76          | ~ (v4_orders_2 @ sk_A)
% 0.54/0.76          | ~ (v3_orders_2 @ sk_A)
% 0.54/0.76          | (v2_struct_0 @ sk_A))),
% 0.54/0.76      inference('sup-', [status(thm)], ['46', '48'])).
% 0.54/0.76  thf('50', plain,
% 0.54/0.76      (((k3_tarski @ (k4_orders_2 @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('51', plain,
% 0.54/0.76      (![X10 : $i]:
% 0.54/0.76         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.54/0.76      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.54/0.76  thf('52', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i]:
% 0.54/0.76         (((X0) = (k1_xboole_0))
% 0.54/0.76          | ~ (r2_hidden @ X0 @ X1)
% 0.54/0.76          | (r2_hidden @ (sk_B @ X0) @ (k3_tarski @ X1)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['35', '37'])).
% 0.54/0.76  thf('53', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (((X0) = (k1_xboole_0))
% 0.54/0.76          | (r2_hidden @ (sk_B @ (sk_B @ X0)) @ (k3_tarski @ X0))
% 0.54/0.76          | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['51', '52'])).
% 0.54/0.76  thf('54', plain,
% 0.54/0.76      (![X8 : $i, X9 : $i]: (~ (r2_hidden @ X8 @ X9) | ~ (r1_tarski @ X9 @ X8))),
% 0.54/0.76      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.54/0.76  thf('55', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (((sk_B @ X0) = (k1_xboole_0))
% 0.54/0.76          | ((X0) = (k1_xboole_0))
% 0.54/0.76          | ~ (r1_tarski @ (k3_tarski @ X0) @ (sk_B @ (sk_B @ X0))))),
% 0.54/0.76      inference('sup-', [status(thm)], ['53', '54'])).
% 0.54/0.76  thf('56', plain,
% 0.54/0.76      ((~ (r1_tarski @ k1_xboole_0 @ 
% 0.54/0.76           (sk_B @ (sk_B @ (k4_orders_2 @ sk_A @ sk_B_1))))
% 0.54/0.76        | ((k4_orders_2 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.54/0.76        | ((sk_B @ (k4_orders_2 @ sk_A @ sk_B_1)) = (k1_xboole_0)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['50', '55'])).
% 0.54/0.76  thf('57', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.54/0.76      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.54/0.76  thf('58', plain,
% 0.54/0.76      ((((k4_orders_2 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.54/0.76        | ((sk_B @ (k4_orders_2 @ sk_A @ sk_B_1)) = (k1_xboole_0)))),
% 0.54/0.76      inference('demod', [status(thm)], ['56', '57'])).
% 0.54/0.76  thf('59', plain,
% 0.54/0.76      (![X10 : $i]:
% 0.54/0.76         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.54/0.76      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.54/0.76  thf('60', plain,
% 0.54/0.76      (((r2_hidden @ k1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.54/0.76        | ((k4_orders_2 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.54/0.76        | ((k4_orders_2 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.54/0.76      inference('sup+', [status(thm)], ['58', '59'])).
% 0.54/0.76  thf('61', plain,
% 0.54/0.76      ((((k4_orders_2 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.54/0.76        | (r2_hidden @ k1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1)))),
% 0.54/0.76      inference('simplify', [status(thm)], ['60'])).
% 0.54/0.76  thf('62', plain,
% 0.54/0.76      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('63', plain,
% 0.54/0.76      (![X20 : $i, X21 : $i, X22 : $i, X24 : $i]:
% 0.54/0.76         (~ (m1_orders_1 @ X20 @ (k1_orders_1 @ (u1_struct_0 @ X21)))
% 0.54/0.76          | ((X22) != (k4_orders_2 @ X21 @ X20))
% 0.54/0.76          | (m2_orders_2 @ X24 @ X21 @ X20)
% 0.54/0.76          | ~ (r2_hidden @ X24 @ X22)
% 0.54/0.76          | ~ (l1_orders_2 @ X21)
% 0.54/0.76          | ~ (v5_orders_2 @ X21)
% 0.54/0.76          | ~ (v4_orders_2 @ X21)
% 0.54/0.76          | ~ (v3_orders_2 @ X21)
% 0.54/0.76          | (v2_struct_0 @ X21))),
% 0.54/0.76      inference('cnf', [status(esa)], [d17_orders_2])).
% 0.54/0.76  thf('64', plain,
% 0.54/0.76      (![X20 : $i, X21 : $i, X24 : $i]:
% 0.54/0.76         ((v2_struct_0 @ X21)
% 0.54/0.76          | ~ (v3_orders_2 @ X21)
% 0.54/0.76          | ~ (v4_orders_2 @ X21)
% 0.54/0.76          | ~ (v5_orders_2 @ X21)
% 0.54/0.76          | ~ (l1_orders_2 @ X21)
% 0.54/0.76          | ~ (r2_hidden @ X24 @ (k4_orders_2 @ X21 @ X20))
% 0.54/0.76          | (m2_orders_2 @ X24 @ X21 @ X20)
% 0.54/0.76          | ~ (m1_orders_1 @ X20 @ (k1_orders_1 @ (u1_struct_0 @ X21))))),
% 0.54/0.76      inference('simplify', [status(thm)], ['63'])).
% 0.54/0.76  thf('65', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         ((m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.54/0.76          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.54/0.76          | ~ (l1_orders_2 @ sk_A)
% 0.54/0.76          | ~ (v5_orders_2 @ sk_A)
% 0.54/0.76          | ~ (v4_orders_2 @ sk_A)
% 0.54/0.76          | ~ (v3_orders_2 @ sk_A)
% 0.54/0.76          | (v2_struct_0 @ sk_A))),
% 0.54/0.76      inference('sup-', [status(thm)], ['62', '64'])).
% 0.54/0.76  thf('66', plain, ((l1_orders_2 @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('67', plain, ((v5_orders_2 @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('68', plain, ((v4_orders_2 @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('69', plain, ((v3_orders_2 @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('70', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         ((m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.54/0.76          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.54/0.76          | (v2_struct_0 @ sk_A))),
% 0.54/0.76      inference('demod', [status(thm)], ['65', '66', '67', '68', '69'])).
% 0.54/0.76  thf('71', plain, (~ (v2_struct_0 @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('72', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.54/0.76          | (m2_orders_2 @ X0 @ sk_A @ sk_B_1))),
% 0.54/0.76      inference('clc', [status(thm)], ['70', '71'])).
% 0.54/0.76  thf('73', plain,
% 0.54/0.76      ((((k4_orders_2 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.54/0.76        | (m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1))),
% 0.54/0.76      inference('sup-', [status(thm)], ['61', '72'])).
% 0.54/0.76  thf('74', plain,
% 0.54/0.76      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('75', plain,
% 0.54/0.76      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.54/0.76         (~ (l1_orders_2 @ X26)
% 0.54/0.76          | ~ (v5_orders_2 @ X26)
% 0.54/0.76          | ~ (v4_orders_2 @ X26)
% 0.54/0.76          | ~ (v3_orders_2 @ X26)
% 0.54/0.76          | (v2_struct_0 @ X26)
% 0.54/0.76          | ~ (m1_orders_1 @ X27 @ (k1_orders_1 @ (u1_struct_0 @ X26)))
% 0.54/0.76          | (v6_orders_2 @ X28 @ X26)
% 0.54/0.76          | ~ (m2_orders_2 @ X28 @ X26 @ X27))),
% 0.54/0.76      inference('cnf', [status(esa)], [dt_m2_orders_2])).
% 0.54/0.76  thf('76', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.54/0.76          | (v6_orders_2 @ X0 @ sk_A)
% 0.54/0.76          | (v2_struct_0 @ sk_A)
% 0.54/0.76          | ~ (v3_orders_2 @ sk_A)
% 0.54/0.76          | ~ (v4_orders_2 @ sk_A)
% 0.54/0.76          | ~ (v5_orders_2 @ sk_A)
% 0.54/0.76          | ~ (l1_orders_2 @ sk_A))),
% 0.54/0.76      inference('sup-', [status(thm)], ['74', '75'])).
% 0.54/0.76  thf('77', plain, ((v3_orders_2 @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('78', plain, ((v4_orders_2 @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('79', plain, ((v5_orders_2 @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('80', plain, ((l1_orders_2 @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('81', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.54/0.76          | (v6_orders_2 @ X0 @ sk_A)
% 0.54/0.76          | (v2_struct_0 @ sk_A))),
% 0.54/0.76      inference('demod', [status(thm)], ['76', '77', '78', '79', '80'])).
% 0.54/0.76  thf('82', plain, (~ (v2_struct_0 @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('83', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         ((v6_orders_2 @ X0 @ sk_A) | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1))),
% 0.54/0.76      inference('clc', [status(thm)], ['81', '82'])).
% 0.54/0.76  thf('84', plain,
% 0.54/0.76      ((((k4_orders_2 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.54/0.76        | (v6_orders_2 @ k1_xboole_0 @ sk_A))),
% 0.54/0.76      inference('sup-', [status(thm)], ['73', '83'])).
% 0.54/0.76  thf('85', plain,
% 0.54/0.76      ((r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ (k4_orders_2 @ sk_A @ sk_B_1))),
% 0.54/0.76      inference('sup-', [status(thm)], ['22', '33'])).
% 0.54/0.76  thf('86', plain,
% 0.54/0.76      (![X8 : $i, X9 : $i]: (~ (r2_hidden @ X8 @ X9) | ~ (r1_tarski @ X9 @ X8))),
% 0.54/0.76      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.54/0.76  thf('87', plain,
% 0.54/0.76      (~ (r1_tarski @ (k4_orders_2 @ sk_A @ sk_B_1) @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.54/0.76      inference('sup-', [status(thm)], ['85', '86'])).
% 0.54/0.76  thf('88', plain,
% 0.54/0.76      ((~ (r1_tarski @ k1_xboole_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.54/0.76        | (v6_orders_2 @ k1_xboole_0 @ sk_A))),
% 0.54/0.76      inference('sup-', [status(thm)], ['84', '87'])).
% 0.54/0.76  thf('89', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.54/0.76      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.54/0.76  thf('90', plain, ((v6_orders_2 @ k1_xboole_0 @ sk_A)),
% 0.54/0.76      inference('demod', [status(thm)], ['88', '89'])).
% 0.54/0.76  thf('91', plain, ((l1_orders_2 @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('92', plain, ((v5_orders_2 @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('93', plain, ((v4_orders_2 @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('94', plain, ((v3_orders_2 @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('95', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (~ (m1_orders_1 @ X0 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))
% 0.54/0.76          | ~ (m2_orders_2 @ k1_xboole_0 @ sk_A @ X0)
% 0.54/0.76          | (v2_struct_0 @ sk_A))),
% 0.54/0.76      inference('demod', [status(thm)], ['49', '90', '91', '92', '93', '94'])).
% 0.54/0.76  thf('96', plain, (~ (v2_struct_0 @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('97', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (~ (m2_orders_2 @ k1_xboole_0 @ sk_A @ X0)
% 0.54/0.76          | ~ (m1_orders_1 @ X0 @ (k1_orders_1 @ (u1_struct_0 @ sk_A))))),
% 0.54/0.76      inference('clc', [status(thm)], ['95', '96'])).
% 0.54/0.76  thf('98', plain, (~ (m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1)),
% 0.54/0.76      inference('sup-', [status(thm)], ['0', '97'])).
% 0.54/0.76  thf('99', plain, ((m2_orders_2 @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A @ sk_B_1)),
% 0.54/0.76      inference('clc', [status(thm)], ['8', '9'])).
% 0.54/0.76  thf('100', plain, (((sk_C_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 0.54/0.76      inference('demod', [status(thm)], ['43', '44'])).
% 0.54/0.76  thf('101', plain, ((m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1)),
% 0.54/0.76      inference('demod', [status(thm)], ['99', '100'])).
% 0.54/0.76  thf('102', plain, ($false), inference('demod', [status(thm)], ['98', '101'])).
% 0.54/0.76  
% 0.54/0.76  % SZS output end Refutation
% 0.54/0.76  
% 0.54/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
