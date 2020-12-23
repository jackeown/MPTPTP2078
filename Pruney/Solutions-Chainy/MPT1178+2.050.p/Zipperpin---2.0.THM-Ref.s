%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bps7E00Sg0

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:27 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 564 expanded)
%              Number of leaves         :   39 ( 186 expanded)
%              Depth                    :   19
%              Number of atoms          : 1098 (6264 expanded)
%              Number of equality atoms :   40 ( 297 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_orders_2_type,type,(
    k4_orders_2: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf('1',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( l1_orders_2 @ X47 )
      | ~ ( v5_orders_2 @ X47 )
      | ~ ( v4_orders_2 @ X47 )
      | ~ ( v3_orders_2 @ X47 )
      | ( v2_struct_0 @ X47 )
      | ~ ( m1_orders_1 @ X48 @ ( k1_orders_1 @ ( u1_struct_0 @ X47 ) ) )
      | ( m2_orders_2 @ ( sk_C_2 @ X48 @ X47 ) @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[existence_m2_orders_2])).

thf('2',plain,
    ( ( m2_orders_2 @ ( sk_C_2 @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( m2_orders_2 @ ( sk_C_2 @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3','4','5','6'])).

thf('8',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m2_orders_2 @ ( sk_C_2 @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_orders_1 @ X41 @ ( k1_orders_1 @ ( u1_struct_0 @ X42 ) ) )
      | ( X43
       != ( k4_orders_2 @ X42 @ X41 ) )
      | ( r2_hidden @ X44 @ X43 )
      | ~ ( m2_orders_2 @ X44 @ X42 @ X41 )
      | ~ ( l1_orders_2 @ X42 )
      | ~ ( v5_orders_2 @ X42 )
      | ~ ( v4_orders_2 @ X42 )
      | ~ ( v3_orders_2 @ X42 )
      | ( v2_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d17_orders_2])).

thf('12',plain,(
    ! [X41: $i,X42: $i,X44: $i] :
      ( ( v2_struct_0 @ X42 )
      | ~ ( v3_orders_2 @ X42 )
      | ~ ( v4_orders_2 @ X42 )
      | ~ ( v5_orders_2 @ X42 )
      | ~ ( l1_orders_2 @ X42 )
      | ~ ( m2_orders_2 @ X44 @ X42 @ X41 )
      | ( r2_hidden @ X44 @ ( k4_orders_2 @ X42 @ X41 ) )
      | ~ ( m1_orders_1 @ X41 @ ( k1_orders_1 @ ( u1_struct_0 @ X42 ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf('19',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    r2_hidden @ ( sk_C_2 @ sk_B_1 @ sk_A ) @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['9','20'])).

thf(t82_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X24 @ X25 ) @ ( k4_xboole_0 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t82_xboole_1])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('23',plain,(
    ! [X17: $i] :
      ( r1_xboole_0 @ X17 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t72_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( ( k2_xboole_0 @ A @ B )
          = ( k2_xboole_0 @ C @ D ) )
        & ( r1_xboole_0 @ C @ A )
        & ( r1_xboole_0 @ D @ B ) )
     => ( C = B ) ) )).

thf('24',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( X21 = X20 )
      | ~ ( r1_xboole_0 @ X21 @ X22 )
      | ( ( k2_xboole_0 @ X22 @ X20 )
       != ( k2_xboole_0 @ X21 @ X23 ) )
      | ~ ( r1_xboole_0 @ X23 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t72_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ~ ( r1_xboole_0 @ X1 @ X1 )
      | ( X1 = X0 ) ) ),
    inference(eq_res,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','26'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('28',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('30',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X27 ) @ X28 )
      | ( r2_hidden @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('31',plain,
    ( ( k3_tarski @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t100_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ) )).

thf('32',plain,(
    ! [X29: $i] :
      ( r1_tarski @ X29 @ ( k1_zfmisc_1 @ ( k3_tarski @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t100_zfmisc_1])).

thf('33',plain,(
    r1_tarski @ ( k4_orders_2 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(t1_zfmisc_1,axiom,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) )).

thf('34',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('35',plain,(
    r1_tarski @ ( k4_orders_2 @ sk_A @ sk_B_1 ) @ ( k1_tarski @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('36',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_xboole_0 @ X15 @ X16 )
      | ( r1_xboole_0 @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) @ X0 )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','37'])).

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

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('40',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) @ k1_xboole_0 ) @ X0 )
      | ( r2_hidden @ k1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['29','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','37'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ~ ( r1_xboole_0 @ X1 @ X1 )
      | ( X1 = X0 ) ) ),
    inference(eq_res,[status(thm)],['24'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ( X0
        = ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( r2_hidden @ k1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    | ( ( k4_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) @ k1_xboole_0 )
      = ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    | ( r2_hidden @ k1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,
    ( ( ( k4_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) @ k1_xboole_0 )
      = ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    | ( r2_hidden @ k1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    m1_orders_1 @ sk_B_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X41: $i,X42: $i,X43: $i,X45: $i] :
      ( ~ ( m1_orders_1 @ X41 @ ( k1_orders_1 @ ( u1_struct_0 @ X42 ) ) )
      | ( X43
       != ( k4_orders_2 @ X42 @ X41 ) )
      | ( m2_orders_2 @ X45 @ X42 @ X41 )
      | ~ ( r2_hidden @ X45 @ X43 )
      | ~ ( l1_orders_2 @ X42 )
      | ~ ( v5_orders_2 @ X42 )
      | ~ ( v4_orders_2 @ X42 )
      | ~ ( v3_orders_2 @ X42 )
      | ( v2_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d17_orders_2])).

thf('51',plain,(
    ! [X41: $i,X42: $i,X45: $i] :
      ( ( v2_struct_0 @ X42 )
      | ~ ( v3_orders_2 @ X42 )
      | ~ ( v4_orders_2 @ X42 )
      | ~ ( v5_orders_2 @ X42 )
      | ~ ( l1_orders_2 @ X42 )
      | ~ ( r2_hidden @ X45 @ ( k4_orders_2 @ X42 @ X41 ) )
      | ( m2_orders_2 @ X45 @ X42 @ X41 )
      | ~ ( m1_orders_1 @ X41 @ ( k1_orders_1 @ ( u1_struct_0 @ X42 ) ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53','54','55','56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( k4_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) @ k1_xboole_0 )
      = ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    | ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['48','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ X0 )
      | ( ( k3_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( k4_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( r2_hidden @ k1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('67',plain,
    ( ( ( k4_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('69',plain,(
    ! [X17: $i] :
      ( r1_xboole_0 @ X17 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('75',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ X0 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['68','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) @ k1_xboole_0 )
      | ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['67','80'])).

thf('82',plain,(
    ! [X17: $i] :
      ( r1_xboole_0 @ X17 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1 )
      | ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['60','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1 ),
    inference('sup-',[status(thm)],['21','86'])).

thf('88',plain,(
    m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1 ),
    inference('sup-',[status(thm)],['21','86'])).

thf('89',plain,(
    m1_orders_1 @ sk_B_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t82_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m2_orders_2 @ C @ A @ B )
             => ! [D: $i] :
                  ( ( m2_orders_2 @ D @ A @ B )
                 => ~ ( r1_xboole_0 @ C @ D ) ) ) ) ) )).

thf('90',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ~ ( m1_orders_1 @ X51 @ ( k1_orders_1 @ ( u1_struct_0 @ X52 ) ) )
      | ~ ( m2_orders_2 @ X53 @ X52 @ X51 )
      | ~ ( r1_xboole_0 @ X54 @ X53 )
      | ~ ( m2_orders_2 @ X54 @ X52 @ X51 )
      | ~ ( l1_orders_2 @ X52 )
      | ~ ( v5_orders_2 @ X52 )
      | ~ ( v4_orders_2 @ X52 )
      | ~ ( v3_orders_2 @ X52 )
      | ( v2_struct_0 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t82_orders_2])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['91','92','93','94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['88','96'])).

thf('98',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('99',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X13 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('102',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['97','102'])).

thf('104',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X0: $i] :
      ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,(
    $false ),
    inference('sup-',[status(thm)],['87','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bps7E00Sg0
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:32:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.53/0.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.53/0.74  % Solved by: fo/fo7.sh
% 0.53/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.74  % done 766 iterations in 0.294s
% 0.53/0.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.53/0.74  % SZS output start Refutation
% 0.53/0.74  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.53/0.74  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.53/0.74  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.53/0.74  thf(k4_orders_2_type, type, k4_orders_2: $i > $i > $i).
% 0.53/0.74  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.53/0.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.53/0.74  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.53/0.74  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.53/0.74  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.53/0.74  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.53/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.74  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.53/0.74  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.53/0.74  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.53/0.74  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.53/0.74  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.53/0.74  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.53/0.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.53/0.74  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.53/0.74  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.53/0.74  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.53/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.74  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.53/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.74  thf(t87_orders_2, conjecture,
% 0.53/0.74    (![A:$i]:
% 0.53/0.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.53/0.74         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.53/0.74       ( ![B:$i]:
% 0.53/0.74         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.74           ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ))).
% 0.53/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.74    (~( ![A:$i]:
% 0.53/0.74        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.53/0.74            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.53/0.74          ( ![B:$i]:
% 0.53/0.74            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.74              ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ) )),
% 0.53/0.74    inference('cnf.neg', [status(esa)], [t87_orders_2])).
% 0.53/0.74  thf('0', plain,
% 0.53/0.74      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf(existence_m2_orders_2, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.53/0.74         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.53/0.74         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.53/0.74       ( ?[C:$i]: ( m2_orders_2 @ C @ A @ B ) ) ))).
% 0.53/0.74  thf('1', plain,
% 0.53/0.74      (![X47 : $i, X48 : $i]:
% 0.53/0.74         (~ (l1_orders_2 @ X47)
% 0.53/0.74          | ~ (v5_orders_2 @ X47)
% 0.53/0.74          | ~ (v4_orders_2 @ X47)
% 0.53/0.74          | ~ (v3_orders_2 @ X47)
% 0.53/0.74          | (v2_struct_0 @ X47)
% 0.53/0.74          | ~ (m1_orders_1 @ X48 @ (k1_orders_1 @ (u1_struct_0 @ X47)))
% 0.53/0.74          | (m2_orders_2 @ (sk_C_2 @ X48 @ X47) @ X47 @ X48))),
% 0.53/0.74      inference('cnf', [status(esa)], [existence_m2_orders_2])).
% 0.53/0.74  thf('2', plain,
% 0.53/0.74      (((m2_orders_2 @ (sk_C_2 @ sk_B_1 @ sk_A) @ sk_A @ sk_B_1)
% 0.53/0.74        | (v2_struct_0 @ sk_A)
% 0.53/0.74        | ~ (v3_orders_2 @ sk_A)
% 0.53/0.74        | ~ (v4_orders_2 @ sk_A)
% 0.53/0.74        | ~ (v5_orders_2 @ sk_A)
% 0.53/0.74        | ~ (l1_orders_2 @ sk_A))),
% 0.53/0.74      inference('sup-', [status(thm)], ['0', '1'])).
% 0.53/0.74  thf('3', plain, ((v3_orders_2 @ sk_A)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('4', plain, ((v4_orders_2 @ sk_A)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('5', plain, ((v5_orders_2 @ sk_A)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('6', plain, ((l1_orders_2 @ sk_A)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('7', plain,
% 0.53/0.74      (((m2_orders_2 @ (sk_C_2 @ sk_B_1 @ sk_A) @ sk_A @ sk_B_1)
% 0.53/0.74        | (v2_struct_0 @ sk_A))),
% 0.53/0.74      inference('demod', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.53/0.74  thf('8', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('9', plain, ((m2_orders_2 @ (sk_C_2 @ sk_B_1 @ sk_A) @ sk_A @ sk_B_1)),
% 0.53/0.74      inference('clc', [status(thm)], ['7', '8'])).
% 0.53/0.74  thf('10', plain,
% 0.53/0.74      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf(d17_orders_2, axiom,
% 0.53/0.74    (![A:$i]:
% 0.53/0.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.53/0.74         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.53/0.74       ( ![B:$i]:
% 0.53/0.74         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.74           ( ![C:$i]:
% 0.53/0.74             ( ( ( C ) = ( k4_orders_2 @ A @ B ) ) <=>
% 0.53/0.74               ( ![D:$i]:
% 0.53/0.74                 ( ( r2_hidden @ D @ C ) <=> ( m2_orders_2 @ D @ A @ B ) ) ) ) ) ) ) ))).
% 0.53/0.74  thf('11', plain,
% 0.53/0.74      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.53/0.74         (~ (m1_orders_1 @ X41 @ (k1_orders_1 @ (u1_struct_0 @ X42)))
% 0.53/0.74          | ((X43) != (k4_orders_2 @ X42 @ X41))
% 0.53/0.74          | (r2_hidden @ X44 @ X43)
% 0.53/0.74          | ~ (m2_orders_2 @ X44 @ X42 @ X41)
% 0.53/0.74          | ~ (l1_orders_2 @ X42)
% 0.53/0.74          | ~ (v5_orders_2 @ X42)
% 0.53/0.74          | ~ (v4_orders_2 @ X42)
% 0.53/0.74          | ~ (v3_orders_2 @ X42)
% 0.53/0.74          | (v2_struct_0 @ X42))),
% 0.53/0.74      inference('cnf', [status(esa)], [d17_orders_2])).
% 0.53/0.74  thf('12', plain,
% 0.53/0.74      (![X41 : $i, X42 : $i, X44 : $i]:
% 0.53/0.74         ((v2_struct_0 @ X42)
% 0.53/0.74          | ~ (v3_orders_2 @ X42)
% 0.53/0.74          | ~ (v4_orders_2 @ X42)
% 0.53/0.74          | ~ (v5_orders_2 @ X42)
% 0.53/0.74          | ~ (l1_orders_2 @ X42)
% 0.53/0.74          | ~ (m2_orders_2 @ X44 @ X42 @ X41)
% 0.53/0.74          | (r2_hidden @ X44 @ (k4_orders_2 @ X42 @ X41))
% 0.53/0.74          | ~ (m1_orders_1 @ X41 @ (k1_orders_1 @ (u1_struct_0 @ X42))))),
% 0.53/0.74      inference('simplify', [status(thm)], ['11'])).
% 0.53/0.74  thf('13', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         ((r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.53/0.74          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.53/0.74          | ~ (l1_orders_2 @ sk_A)
% 0.53/0.74          | ~ (v5_orders_2 @ sk_A)
% 0.53/0.74          | ~ (v4_orders_2 @ sk_A)
% 0.53/0.74          | ~ (v3_orders_2 @ sk_A)
% 0.53/0.74          | (v2_struct_0 @ sk_A))),
% 0.53/0.74      inference('sup-', [status(thm)], ['10', '12'])).
% 0.53/0.74  thf('14', plain, ((l1_orders_2 @ sk_A)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('15', plain, ((v5_orders_2 @ sk_A)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('16', plain, ((v4_orders_2 @ sk_A)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('17', plain, ((v3_orders_2 @ sk_A)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('18', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         ((r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.53/0.74          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.53/0.74          | (v2_struct_0 @ sk_A))),
% 0.53/0.74      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.53/0.74  thf('19', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('20', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.53/0.74          | (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1)))),
% 0.53/0.74      inference('clc', [status(thm)], ['18', '19'])).
% 0.53/0.74  thf('21', plain,
% 0.53/0.74      ((r2_hidden @ (sk_C_2 @ sk_B_1 @ sk_A) @ (k4_orders_2 @ sk_A @ sk_B_1))),
% 0.53/0.74      inference('sup-', [status(thm)], ['9', '20'])).
% 0.53/0.74  thf(t82_xboole_1, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ))).
% 0.53/0.74  thf('22', plain,
% 0.53/0.74      (![X24 : $i, X25 : $i]:
% 0.53/0.74         (r1_xboole_0 @ (k4_xboole_0 @ X24 @ X25) @ (k4_xboole_0 @ X25 @ X24))),
% 0.53/0.74      inference('cnf', [status(esa)], [t82_xboole_1])).
% 0.53/0.74  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.53/0.74  thf('23', plain, (![X17 : $i]: (r1_xboole_0 @ X17 @ k1_xboole_0)),
% 0.53/0.74      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.53/0.74  thf(t72_xboole_1, axiom,
% 0.53/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.74     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.53/0.74         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.53/0.74       ( ( C ) = ( B ) ) ))).
% 0.53/0.74  thf('24', plain,
% 0.53/0.74      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.53/0.74         (((X21) = (X20))
% 0.53/0.74          | ~ (r1_xboole_0 @ X21 @ X22)
% 0.53/0.74          | ((k2_xboole_0 @ X22 @ X20) != (k2_xboole_0 @ X21 @ X23))
% 0.53/0.74          | ~ (r1_xboole_0 @ X23 @ X20))),
% 0.53/0.74      inference('cnf', [status(esa)], [t72_xboole_1])).
% 0.53/0.74  thf('25', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (~ (r1_xboole_0 @ X0 @ X0) | ~ (r1_xboole_0 @ X1 @ X1) | ((X1) = (X0)))),
% 0.53/0.74      inference('eq_res', [status(thm)], ['24'])).
% 0.53/0.74  thf('26', plain,
% 0.53/0.74      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['23', '25'])).
% 0.53/0.74  thf('27', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['22', '26'])).
% 0.53/0.74  thf(t48_xboole_1, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.53/0.74  thf('28', plain,
% 0.53/0.74      (![X11 : $i, X12 : $i]:
% 0.53/0.74         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.53/0.74           = (k3_xboole_0 @ X11 @ X12))),
% 0.53/0.74      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.53/0.74  thf('29', plain,
% 0.53/0.74      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.53/0.74      inference('sup+', [status(thm)], ['27', '28'])).
% 0.53/0.74  thf(l27_zfmisc_1, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.53/0.74  thf('30', plain,
% 0.53/0.74      (![X27 : $i, X28 : $i]:
% 0.53/0.74         ((r1_xboole_0 @ (k1_tarski @ X27) @ X28) | (r2_hidden @ X27 @ X28))),
% 0.53/0.74      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.53/0.74  thf('31', plain,
% 0.53/0.74      (((k3_tarski @ (k4_orders_2 @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf(t100_zfmisc_1, axiom,
% 0.53/0.74    (![A:$i]: ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ))).
% 0.53/0.74  thf('32', plain,
% 0.53/0.74      (![X29 : $i]: (r1_tarski @ X29 @ (k1_zfmisc_1 @ (k3_tarski @ X29)))),
% 0.53/0.74      inference('cnf', [status(esa)], [t100_zfmisc_1])).
% 0.53/0.74  thf('33', plain,
% 0.53/0.74      ((r1_tarski @ (k4_orders_2 @ sk_A @ sk_B_1) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.53/0.74      inference('sup+', [status(thm)], ['31', '32'])).
% 0.53/0.74  thf(t1_zfmisc_1, axiom,
% 0.53/0.74    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.53/0.74  thf('34', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.53/0.74      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.53/0.74  thf('35', plain,
% 0.53/0.74      ((r1_tarski @ (k4_orders_2 @ sk_A @ sk_B_1) @ (k1_tarski @ k1_xboole_0))),
% 0.53/0.74      inference('demod', [status(thm)], ['33', '34'])).
% 0.53/0.74  thf(t63_xboole_1, axiom,
% 0.53/0.74    (![A:$i,B:$i,C:$i]:
% 0.53/0.74     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.53/0.75       ( r1_xboole_0 @ A @ C ) ))).
% 0.53/0.75  thf('36', plain,
% 0.53/0.75      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.53/0.75         (~ (r1_tarski @ X14 @ X15)
% 0.53/0.75          | ~ (r1_xboole_0 @ X15 @ X16)
% 0.53/0.75          | (r1_xboole_0 @ X14 @ X16))),
% 0.53/0.75      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.53/0.75  thf('37', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((r1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1) @ X0)
% 0.53/0.75          | ~ (r1_xboole_0 @ (k1_tarski @ k1_xboole_0) @ X0))),
% 0.53/0.75      inference('sup-', [status(thm)], ['35', '36'])).
% 0.53/0.75  thf('38', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((r2_hidden @ k1_xboole_0 @ X0)
% 0.53/0.75          | (r1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1) @ X0))),
% 0.53/0.75      inference('sup-', [status(thm)], ['30', '37'])).
% 0.53/0.75  thf(t3_xboole_0, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.53/0.75            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.53/0.75       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.53/0.75            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.53/0.75  thf('39', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.53/0.75      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.53/0.75  thf(t4_xboole_0, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.53/0.75            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.53/0.75       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.53/0.75            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.53/0.75  thf('40', plain,
% 0.53/0.75      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.53/0.75         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.53/0.75          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.53/0.75      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.53/0.75  thf('41', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.75         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.53/0.75          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.53/0.75      inference('sup-', [status(thm)], ['39', '40'])).
% 0.53/0.75  thf('42', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         ((r2_hidden @ k1_xboole_0 @ X0)
% 0.53/0.75          | (r1_xboole_0 @ 
% 0.53/0.75             (k3_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1) @ X0) @ X1))),
% 0.53/0.75      inference('sup-', [status(thm)], ['38', '41'])).
% 0.53/0.75  thf('43', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((r1_xboole_0 @ 
% 0.53/0.75           (k4_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1) @ k1_xboole_0) @ X0)
% 0.53/0.75          | (r2_hidden @ k1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1)))),
% 0.53/0.75      inference('sup+', [status(thm)], ['29', '42'])).
% 0.53/0.75  thf('44', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((r2_hidden @ k1_xboole_0 @ X0)
% 0.53/0.75          | (r1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1) @ X0))),
% 0.53/0.75      inference('sup-', [status(thm)], ['30', '37'])).
% 0.53/0.75  thf('45', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         (~ (r1_xboole_0 @ X0 @ X0) | ~ (r1_xboole_0 @ X1 @ X1) | ((X1) = (X0)))),
% 0.53/0.75      inference('eq_res', [status(thm)], ['24'])).
% 0.53/0.75  thf('46', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((r2_hidden @ k1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.53/0.75          | ((X0) = (k4_orders_2 @ sk_A @ sk_B_1))
% 0.53/0.75          | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.53/0.75      inference('sup-', [status(thm)], ['44', '45'])).
% 0.53/0.75  thf('47', plain,
% 0.53/0.75      (((r2_hidden @ k1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.53/0.75        | ((k4_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1) @ k1_xboole_0)
% 0.53/0.75            = (k4_orders_2 @ sk_A @ sk_B_1))
% 0.53/0.75        | (r2_hidden @ k1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['43', '46'])).
% 0.53/0.75  thf('48', plain,
% 0.53/0.75      ((((k4_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1) @ k1_xboole_0)
% 0.53/0.75          = (k4_orders_2 @ sk_A @ sk_B_1))
% 0.53/0.75        | (r2_hidden @ k1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1)))),
% 0.53/0.75      inference('simplify', [status(thm)], ['47'])).
% 0.53/0.75  thf('49', plain,
% 0.53/0.75      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('50', plain,
% 0.53/0.75      (![X41 : $i, X42 : $i, X43 : $i, X45 : $i]:
% 0.53/0.75         (~ (m1_orders_1 @ X41 @ (k1_orders_1 @ (u1_struct_0 @ X42)))
% 0.53/0.75          | ((X43) != (k4_orders_2 @ X42 @ X41))
% 0.53/0.75          | (m2_orders_2 @ X45 @ X42 @ X41)
% 0.53/0.75          | ~ (r2_hidden @ X45 @ X43)
% 0.53/0.75          | ~ (l1_orders_2 @ X42)
% 0.53/0.75          | ~ (v5_orders_2 @ X42)
% 0.53/0.75          | ~ (v4_orders_2 @ X42)
% 0.53/0.75          | ~ (v3_orders_2 @ X42)
% 0.53/0.75          | (v2_struct_0 @ X42))),
% 0.53/0.75      inference('cnf', [status(esa)], [d17_orders_2])).
% 0.53/0.75  thf('51', plain,
% 0.53/0.75      (![X41 : $i, X42 : $i, X45 : $i]:
% 0.53/0.75         ((v2_struct_0 @ X42)
% 0.53/0.75          | ~ (v3_orders_2 @ X42)
% 0.53/0.75          | ~ (v4_orders_2 @ X42)
% 0.53/0.75          | ~ (v5_orders_2 @ X42)
% 0.53/0.75          | ~ (l1_orders_2 @ X42)
% 0.53/0.75          | ~ (r2_hidden @ X45 @ (k4_orders_2 @ X42 @ X41))
% 0.53/0.75          | (m2_orders_2 @ X45 @ X42 @ X41)
% 0.53/0.75          | ~ (m1_orders_1 @ X41 @ (k1_orders_1 @ (u1_struct_0 @ X42))))),
% 0.53/0.75      inference('simplify', [status(thm)], ['50'])).
% 0.53/0.75  thf('52', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.53/0.75          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.53/0.75          | ~ (l1_orders_2 @ sk_A)
% 0.53/0.75          | ~ (v5_orders_2 @ sk_A)
% 0.53/0.75          | ~ (v4_orders_2 @ sk_A)
% 0.53/0.75          | ~ (v3_orders_2 @ sk_A)
% 0.53/0.75          | (v2_struct_0 @ sk_A))),
% 0.53/0.75      inference('sup-', [status(thm)], ['49', '51'])).
% 0.53/0.75  thf('53', plain, ((l1_orders_2 @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('54', plain, ((v5_orders_2 @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('55', plain, ((v4_orders_2 @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('56', plain, ((v3_orders_2 @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('57', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.53/0.75          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.53/0.75          | (v2_struct_0 @ sk_A))),
% 0.53/0.75      inference('demod', [status(thm)], ['52', '53', '54', '55', '56'])).
% 0.53/0.75  thf('58', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('59', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.53/0.75          | (m2_orders_2 @ X0 @ sk_A @ sk_B_1))),
% 0.53/0.75      inference('clc', [status(thm)], ['57', '58'])).
% 0.53/0.75  thf('60', plain,
% 0.53/0.75      ((((k4_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1) @ k1_xboole_0)
% 0.53/0.75          = (k4_orders_2 @ sk_A @ sk_B_1))
% 0.53/0.75        | (m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1))),
% 0.53/0.75      inference('sup-', [status(thm)], ['48', '59'])).
% 0.53/0.75  thf('61', plain,
% 0.53/0.75      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.53/0.75      inference('sup+', [status(thm)], ['27', '28'])).
% 0.53/0.75  thf('62', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         ((r2_hidden @ k1_xboole_0 @ X0)
% 0.53/0.75          | (r1_xboole_0 @ 
% 0.53/0.75             (k3_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1) @ X0) @ X1))),
% 0.53/0.75      inference('sup-', [status(thm)], ['38', '41'])).
% 0.53/0.75  thf('63', plain,
% 0.53/0.75      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.53/0.75      inference('sup-', [status(thm)], ['23', '25'])).
% 0.53/0.75  thf('64', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((r2_hidden @ k1_xboole_0 @ X0)
% 0.53/0.75          | ((k3_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1) @ X0) = (k1_xboole_0)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['62', '63'])).
% 0.53/0.75  thf('65', plain,
% 0.53/0.75      ((((k4_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1) @ k1_xboole_0)
% 0.53/0.75          = (k1_xboole_0))
% 0.53/0.75        | (r2_hidden @ k1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1)))),
% 0.53/0.75      inference('sup+', [status(thm)], ['61', '64'])).
% 0.53/0.75  thf('66', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.53/0.75          | (m2_orders_2 @ X0 @ sk_A @ sk_B_1))),
% 0.53/0.75      inference('clc', [status(thm)], ['57', '58'])).
% 0.53/0.75  thf('67', plain,
% 0.53/0.75      ((((k4_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1) @ k1_xboole_0)
% 0.53/0.75          = (k1_xboole_0))
% 0.53/0.75        | (m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1))),
% 0.53/0.75      inference('sup-', [status(thm)], ['65', '66'])).
% 0.53/0.75  thf('68', plain,
% 0.53/0.75      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.53/0.75      inference('sup+', [status(thm)], ['27', '28'])).
% 0.53/0.75  thf('69', plain, (![X17 : $i]: (r1_xboole_0 @ X17 @ k1_xboole_0)),
% 0.53/0.75      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.53/0.75  thf('70', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.75         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.53/0.75          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.53/0.75      inference('sup-', [status(thm)], ['39', '40'])).
% 0.53/0.75  thf('71', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         (r1_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X1)),
% 0.53/0.75      inference('sup-', [status(thm)], ['69', '70'])).
% 0.53/0.75  thf('72', plain,
% 0.53/0.75      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.53/0.75      inference('sup-', [status(thm)], ['23', '25'])).
% 0.53/0.75  thf('73', plain,
% 0.53/0.75      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.53/0.75      inference('sup-', [status(thm)], ['71', '72'])).
% 0.53/0.75  thf('74', plain,
% 0.53/0.75      (![X11 : $i, X12 : $i]:
% 0.53/0.75         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.53/0.75           = (k3_xboole_0 @ X11 @ X12))),
% 0.53/0.75      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.53/0.75  thf('75', plain,
% 0.53/0.75      (![X11 : $i, X12 : $i]:
% 0.53/0.75         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.53/0.75           = (k3_xboole_0 @ X11 @ X12))),
% 0.53/0.75      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.53/0.75  thf('76', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.53/0.75           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.53/0.75      inference('sup+', [status(thm)], ['74', '75'])).
% 0.53/0.75  thf('77', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.53/0.75           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.53/0.75      inference('sup+', [status(thm)], ['73', '76'])).
% 0.53/0.75  thf('78', plain,
% 0.53/0.75      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.53/0.75         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.53/0.75          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.53/0.75      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.53/0.75  thf('79', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ k1_xboole_0))
% 0.53/0.75          | ~ (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['77', '78'])).
% 0.53/0.75  thf('80', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         (~ (r2_hidden @ X1 @ (k3_xboole_0 @ X0 @ X0))
% 0.53/0.75          | ~ (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['68', '79'])).
% 0.53/0.75  thf('81', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (~ (r1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1) @ k1_xboole_0)
% 0.53/0.75          | (m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1)
% 0.53/0.75          | ~ (r2_hidden @ X0 @ 
% 0.53/0.75               (k3_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1) @ 
% 0.53/0.75                (k4_orders_2 @ sk_A @ sk_B_1))))),
% 0.53/0.75      inference('sup-', [status(thm)], ['67', '80'])).
% 0.53/0.75  thf('82', plain, (![X17 : $i]: (r1_xboole_0 @ X17 @ k1_xboole_0)),
% 0.53/0.75      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.53/0.75  thf('83', plain,
% 0.53/0.75      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.53/0.75      inference('sup+', [status(thm)], ['27', '28'])).
% 0.53/0.75  thf('84', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1)
% 0.53/0.75          | ~ (r2_hidden @ X0 @ 
% 0.53/0.75               (k4_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1) @ k1_xboole_0)))),
% 0.53/0.75      inference('demod', [status(thm)], ['81', '82', '83'])).
% 0.53/0.75  thf('85', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.53/0.75          | (m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1)
% 0.53/0.75          | (m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1))),
% 0.53/0.75      inference('sup-', [status(thm)], ['60', '84'])).
% 0.53/0.75  thf('86', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1)
% 0.53/0.75          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1)))),
% 0.53/0.75      inference('simplify', [status(thm)], ['85'])).
% 0.53/0.75  thf('87', plain, ((m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1)),
% 0.53/0.75      inference('sup-', [status(thm)], ['21', '86'])).
% 0.53/0.75  thf('88', plain, ((m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1)),
% 0.53/0.75      inference('sup-', [status(thm)], ['21', '86'])).
% 0.53/0.75  thf('89', plain,
% 0.53/0.75      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf(t82_orders_2, axiom,
% 0.53/0.75    (![A:$i]:
% 0.53/0.75     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.53/0.75         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.53/0.75       ( ![B:$i]:
% 0.53/0.75         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.75           ( ![C:$i]:
% 0.53/0.75             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.53/0.75               ( ![D:$i]:
% 0.53/0.75                 ( ( m2_orders_2 @ D @ A @ B ) => ( ~( r1_xboole_0 @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.53/0.75  thf('90', plain,
% 0.53/0.75      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 0.53/0.75         (~ (m1_orders_1 @ X51 @ (k1_orders_1 @ (u1_struct_0 @ X52)))
% 0.53/0.75          | ~ (m2_orders_2 @ X53 @ X52 @ X51)
% 0.53/0.75          | ~ (r1_xboole_0 @ X54 @ X53)
% 0.53/0.75          | ~ (m2_orders_2 @ X54 @ X52 @ X51)
% 0.53/0.75          | ~ (l1_orders_2 @ X52)
% 0.53/0.75          | ~ (v5_orders_2 @ X52)
% 0.53/0.75          | ~ (v4_orders_2 @ X52)
% 0.53/0.75          | ~ (v3_orders_2 @ X52)
% 0.53/0.75          | (v2_struct_0 @ X52))),
% 0.53/0.75      inference('cnf', [status(esa)], [t82_orders_2])).
% 0.53/0.75  thf('91', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         ((v2_struct_0 @ sk_A)
% 0.53/0.75          | ~ (v3_orders_2 @ sk_A)
% 0.53/0.75          | ~ (v4_orders_2 @ sk_A)
% 0.53/0.75          | ~ (v5_orders_2 @ sk_A)
% 0.53/0.75          | ~ (l1_orders_2 @ sk_A)
% 0.53/0.75          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.53/0.75          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.53/0.75          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B_1))),
% 0.53/0.75      inference('sup-', [status(thm)], ['89', '90'])).
% 0.53/0.75  thf('92', plain, ((v3_orders_2 @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('93', plain, ((v4_orders_2 @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('94', plain, ((v5_orders_2 @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('95', plain, ((l1_orders_2 @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('96', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         ((v2_struct_0 @ sk_A)
% 0.53/0.75          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.53/0.75          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.53/0.75          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B_1))),
% 0.53/0.75      inference('demod', [status(thm)], ['91', '92', '93', '94', '95'])).
% 0.53/0.75  thf('97', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.53/0.75          | ~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.53/0.75          | (v2_struct_0 @ sk_A))),
% 0.53/0.75      inference('sup-', [status(thm)], ['88', '96'])).
% 0.53/0.75  thf('98', plain,
% 0.53/0.75      (![X11 : $i, X12 : $i]:
% 0.53/0.75         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.53/0.75           = (k3_xboole_0 @ X11 @ X12))),
% 0.53/0.75      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.53/0.75  thf(t4_boole, axiom,
% 0.53/0.75    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.53/0.75  thf('99', plain,
% 0.53/0.75      (![X13 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X13) = (k1_xboole_0))),
% 0.53/0.75      inference('cnf', [status(esa)], [t4_boole])).
% 0.53/0.75  thf('100', plain,
% 0.53/0.75      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.53/0.75      inference('sup+', [status(thm)], ['98', '99'])).
% 0.53/0.75  thf('101', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         (r1_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X1)),
% 0.53/0.75      inference('sup-', [status(thm)], ['69', '70'])).
% 0.53/0.75  thf('102', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.53/0.75      inference('sup+', [status(thm)], ['100', '101'])).
% 0.53/0.75  thf('103', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1) | (v2_struct_0 @ sk_A))),
% 0.53/0.75      inference('demod', [status(thm)], ['97', '102'])).
% 0.53/0.75  thf('104', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('105', plain, (![X0 : $i]: ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)),
% 0.53/0.75      inference('clc', [status(thm)], ['103', '104'])).
% 0.53/0.75  thf('106', plain, ($false), inference('sup-', [status(thm)], ['87', '105'])).
% 0.53/0.75  
% 0.53/0.75  % SZS output end Refutation
% 0.53/0.75  
% 0.53/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
