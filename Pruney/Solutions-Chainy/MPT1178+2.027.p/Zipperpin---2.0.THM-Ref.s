%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5HboS2WcaY

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:23 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 277 expanded)
%              Number of leaves         :   36 ( 100 expanded)
%              Depth                    :   15
%              Number of atoms          :  801 (3564 expanded)
%              Number of equality atoms :   31 ( 169 expanded)
%              Maximal formula depth    :   19 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r2_wellord1_type,type,(
    r2_wellord1: $i > $i > $o )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_orders_2_type,type,(
    k4_orders_2: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_orders_2_type,type,(
    k1_orders_2: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

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

thf(fc9_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) )
     => ~ ( v1_xboole_0 @ ( k4_orders_2 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_orders_2 @ X21 )
      | ~ ( v5_orders_2 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v3_orders_2 @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_orders_1 @ X22 @ ( k1_orders_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v1_xboole_0 @ ( k4_orders_2 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[fc9_orders_2])).

thf('2',plain,
    ( ~ ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
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
    ( ~ ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3','4','5','6'])).

thf('8',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ~ ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_orders_1 @ sk_B_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k3_tarski @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t34_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) )).

thf('12',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('13',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ ( k3_tarski @ X2 ) )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( sk_B @ X0 ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r1_tarski @ ( sk_B @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) @ k1_xboole_0 )
    | ( ( k4_orders_2 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('17',plain,
    ( ( ( k4_orders_2 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( sk_B @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf('19',plain,
    ( ( r2_hidden @ k1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    | ( ( k4_orders_2 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k4_orders_2 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k4_orders_2 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( r2_hidden @ k1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
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

thf('22',plain,(
    ! [X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ~ ( m1_orders_1 @ X12 @ ( k1_orders_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( X14
       != ( k4_orders_2 @ X13 @ X12 ) )
      | ( m2_orders_2 @ X16 @ X13 @ X12 )
      | ~ ( r2_hidden @ X16 @ X14 )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v3_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d17_orders_2])).

thf('23',plain,(
    ! [X12: $i,X13: $i,X16: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v3_orders_2 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( r2_hidden @ X16 @ ( k4_orders_2 @ X13 @ X12 ) )
      | ( m2_orders_2 @ X16 @ X13 @ X12 )
      | ~ ( m1_orders_1 @ X12 @ ( k1_orders_1 @ ( u1_struct_0 @ X13 ) ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','26','27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k4_orders_2 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['20','31'])).

thf('33',plain,(
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

thf('34',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( l1_orders_2 @ X18 )
      | ~ ( v5_orders_2 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v3_orders_2 @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_orders_1 @ X19 @ ( k1_orders_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m2_orders_2 @ X20 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_orders_2])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36','37','38','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k4_orders_2 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['32','42'])).

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

thf('44',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_orders_1 @ X8 @ ( k1_orders_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( m2_orders_2 @ X10 @ X9 @ X8 )
      | ( X10 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v6_orders_2 @ X10 @ X9 )
      | ~ ( l1_orders_2 @ X9 )
      | ~ ( v5_orders_2 @ X9 )
      | ~ ( v4_orders_2 @ X9 )
      | ~ ( v3_orders_2 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d16_orders_2])).

thf('45',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v3_orders_2 @ X9 )
      | ~ ( v4_orders_2 @ X9 )
      | ~ ( v5_orders_2 @ X9 )
      | ~ ( l1_orders_2 @ X9 )
      | ~ ( v6_orders_2 @ k1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( m2_orders_2 @ k1_xboole_0 @ X9 @ X8 )
      | ~ ( m1_orders_1 @ X8 @ ( k1_orders_1 @ ( u1_struct_0 @ X9 ) ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k4_orders_2 @ sk_A @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( m1_orders_1 @ X0 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m2_orders_2 @ k1_xboole_0 @ sk_A @ X0 )
      | ~ ( v6_orders_2 @ k1_xboole_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,
    ( ( ( k4_orders_2 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['20','31'])).

thf('48',plain,(
    m1_orders_1 @ sk_B_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( l1_orders_2 @ X18 )
      | ~ ( v5_orders_2 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v3_orders_2 @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_orders_1 @ X19 @ ( k1_orders_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v6_orders_2 @ X20 @ X18 )
      | ~ ( m2_orders_2 @ X20 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_orders_2])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( v6_orders_2 @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( v6_orders_2 @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51','52','53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v6_orders_2 @ X0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k4_orders_2 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( v6_orders_2 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','57'])).

thf('59',plain,(
    ~ ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('60',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v6_orders_2 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('61',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('62',plain,(
    v6_orders_2 @ k1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( k4_orders_2 @ sk_A @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( m1_orders_1 @ X0 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m2_orders_2 @ k1_xboole_0 @ sk_A @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','62','63','64','65','66'])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1 )
    | ( ( k4_orders_2 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( ( k4_orders_2 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( k4_orders_2 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['20','31'])).

thf('72',plain,
    ( ( k4_orders_2 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('74',plain,(
    $false ),
    inference(demod,[status(thm)],['9','72','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5HboS2WcaY
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:21:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 50 iterations in 0.021s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.19/0.46  thf(r2_wellord1_type, type, r2_wellord1: $i > $i > $o).
% 0.19/0.46  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.19/0.46  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.46  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.19/0.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.46  thf(k4_orders_2_type, type, k4_orders_2: $i > $i > $i).
% 0.19/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.46  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 0.19/0.46  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.19/0.46  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.19/0.46  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.19/0.46  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.46  thf(k1_orders_2_type, type, k1_orders_2: $i > $i > $i).
% 0.19/0.46  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.46  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.19/0.46  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.19/0.46  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.19/0.46  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.19/0.46  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.19/0.46  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.19/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.46  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.46  thf(t87_orders_2, conjecture,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.19/0.46         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.19/0.46       ( ![B:$i]:
% 0.19/0.46         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.46           ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i]:
% 0.19/0.46        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.19/0.46            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.19/0.46          ( ![B:$i]:
% 0.19/0.46            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.46              ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t87_orders_2])).
% 0.19/0.46  thf('0', plain,
% 0.19/0.46      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(fc9_orders_2, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.19/0.46         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.19/0.46         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.46       ( ~( v1_xboole_0 @ ( k4_orders_2 @ A @ B ) ) ) ))).
% 0.19/0.46  thf('1', plain,
% 0.19/0.46      (![X21 : $i, X22 : $i]:
% 0.19/0.46         (~ (l1_orders_2 @ X21)
% 0.19/0.46          | ~ (v5_orders_2 @ X21)
% 0.19/0.46          | ~ (v4_orders_2 @ X21)
% 0.19/0.46          | ~ (v3_orders_2 @ X21)
% 0.19/0.46          | (v2_struct_0 @ X21)
% 0.19/0.46          | ~ (m1_orders_1 @ X22 @ (k1_orders_1 @ (u1_struct_0 @ X21)))
% 0.19/0.46          | ~ (v1_xboole_0 @ (k4_orders_2 @ X21 @ X22)))),
% 0.19/0.46      inference('cnf', [status(esa)], [fc9_orders_2])).
% 0.19/0.46  thf('2', plain,
% 0.19/0.46      ((~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.19/0.46        | (v2_struct_0 @ sk_A)
% 0.19/0.46        | ~ (v3_orders_2 @ sk_A)
% 0.19/0.46        | ~ (v4_orders_2 @ sk_A)
% 0.19/0.46        | ~ (v5_orders_2 @ sk_A)
% 0.19/0.46        | ~ (l1_orders_2 @ sk_A))),
% 0.19/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.46  thf('3', plain, ((v3_orders_2 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('4', plain, ((v4_orders_2 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('5', plain, ((v5_orders_2 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('6', plain, ((l1_orders_2 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('7', plain,
% 0.19/0.46      ((~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.19/0.46      inference('demod', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.19/0.46  thf('8', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('9', plain, (~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1))),
% 0.19/0.46      inference('clc', [status(thm)], ['7', '8'])).
% 0.19/0.46  thf('10', plain,
% 0.19/0.46      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('11', plain,
% 0.19/0.46      (((k3_tarski @ (k4_orders_2 @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(t34_mcart_1, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.19/0.46          ( ![B:$i]:
% 0.19/0.46            ( ~( ( r2_hidden @ B @ A ) & 
% 0.19/0.46                 ( ![C:$i,D:$i,E:$i,F:$i]:
% 0.19/0.46                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.19/0.46                        ( ( B ) = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.46  thf('12', plain,
% 0.19/0.46      (![X3 : $i]: (((X3) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X3) @ X3))),
% 0.19/0.46      inference('cnf', [status(esa)], [t34_mcart_1])).
% 0.19/0.46  thf(l49_zfmisc_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.19/0.46  thf('13', plain,
% 0.19/0.46      (![X1 : $i, X2 : $i]:
% 0.19/0.46         ((r1_tarski @ X1 @ (k3_tarski @ X2)) | ~ (r2_hidden @ X1 @ X2))),
% 0.19/0.46      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.19/0.46  thf('14', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (((X0) = (k1_xboole_0)) | (r1_tarski @ (sk_B @ X0) @ (k3_tarski @ X0)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.46  thf('15', plain,
% 0.19/0.46      (((r1_tarski @ (sk_B @ (k4_orders_2 @ sk_A @ sk_B_1)) @ k1_xboole_0)
% 0.19/0.46        | ((k4_orders_2 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.19/0.46      inference('sup+', [status(thm)], ['11', '14'])).
% 0.19/0.46  thf(t3_xboole_1, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.46  thf('16', plain,
% 0.19/0.46      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.19/0.46      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.19/0.46  thf('17', plain,
% 0.19/0.46      ((((k4_orders_2 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.19/0.46        | ((sk_B @ (k4_orders_2 @ sk_A @ sk_B_1)) = (k1_xboole_0)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.46  thf('18', plain,
% 0.19/0.46      (![X3 : $i]: (((X3) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X3) @ X3))),
% 0.19/0.46      inference('cnf', [status(esa)], [t34_mcart_1])).
% 0.19/0.46  thf('19', plain,
% 0.19/0.46      (((r2_hidden @ k1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.19/0.46        | ((k4_orders_2 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.19/0.46        | ((k4_orders_2 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.19/0.46      inference('sup+', [status(thm)], ['17', '18'])).
% 0.19/0.46  thf('20', plain,
% 0.19/0.46      ((((k4_orders_2 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.19/0.46        | (r2_hidden @ k1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1)))),
% 0.19/0.46      inference('simplify', [status(thm)], ['19'])).
% 0.19/0.46  thf('21', plain,
% 0.19/0.46      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(d17_orders_2, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.19/0.46         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.19/0.46       ( ![B:$i]:
% 0.19/0.46         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.46           ( ![C:$i]:
% 0.19/0.46             ( ( ( C ) = ( k4_orders_2 @ A @ B ) ) <=>
% 0.19/0.46               ( ![D:$i]:
% 0.19/0.46                 ( ( r2_hidden @ D @ C ) <=> ( m2_orders_2 @ D @ A @ B ) ) ) ) ) ) ) ))).
% 0.19/0.46  thf('22', plain,
% 0.19/0.46      (![X12 : $i, X13 : $i, X14 : $i, X16 : $i]:
% 0.19/0.46         (~ (m1_orders_1 @ X12 @ (k1_orders_1 @ (u1_struct_0 @ X13)))
% 0.19/0.46          | ((X14) != (k4_orders_2 @ X13 @ X12))
% 0.19/0.46          | (m2_orders_2 @ X16 @ X13 @ X12)
% 0.19/0.46          | ~ (r2_hidden @ X16 @ X14)
% 0.19/0.46          | ~ (l1_orders_2 @ X13)
% 0.19/0.46          | ~ (v5_orders_2 @ X13)
% 0.19/0.46          | ~ (v4_orders_2 @ X13)
% 0.19/0.46          | ~ (v3_orders_2 @ X13)
% 0.19/0.46          | (v2_struct_0 @ X13))),
% 0.19/0.46      inference('cnf', [status(esa)], [d17_orders_2])).
% 0.19/0.46  thf('23', plain,
% 0.19/0.46      (![X12 : $i, X13 : $i, X16 : $i]:
% 0.19/0.46         ((v2_struct_0 @ X13)
% 0.19/0.46          | ~ (v3_orders_2 @ X13)
% 0.19/0.46          | ~ (v4_orders_2 @ X13)
% 0.19/0.46          | ~ (v5_orders_2 @ X13)
% 0.19/0.46          | ~ (l1_orders_2 @ X13)
% 0.19/0.46          | ~ (r2_hidden @ X16 @ (k4_orders_2 @ X13 @ X12))
% 0.19/0.46          | (m2_orders_2 @ X16 @ X13 @ X12)
% 0.19/0.46          | ~ (m1_orders_1 @ X12 @ (k1_orders_1 @ (u1_struct_0 @ X13))))),
% 0.19/0.46      inference('simplify', [status(thm)], ['22'])).
% 0.19/0.46  thf('24', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         ((m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.19/0.46          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.19/0.46          | ~ (l1_orders_2 @ sk_A)
% 0.19/0.46          | ~ (v5_orders_2 @ sk_A)
% 0.19/0.46          | ~ (v4_orders_2 @ sk_A)
% 0.19/0.46          | ~ (v3_orders_2 @ sk_A)
% 0.19/0.46          | (v2_struct_0 @ sk_A))),
% 0.19/0.46      inference('sup-', [status(thm)], ['21', '23'])).
% 0.19/0.46  thf('25', plain, ((l1_orders_2 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('26', plain, ((v5_orders_2 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('27', plain, ((v4_orders_2 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('28', plain, ((v3_orders_2 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('29', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         ((m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.19/0.46          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.19/0.46          | (v2_struct_0 @ sk_A))),
% 0.19/0.46      inference('demod', [status(thm)], ['24', '25', '26', '27', '28'])).
% 0.19/0.46  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('31', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.19/0.46          | (m2_orders_2 @ X0 @ sk_A @ sk_B_1))),
% 0.19/0.46      inference('clc', [status(thm)], ['29', '30'])).
% 0.19/0.46  thf('32', plain,
% 0.19/0.46      ((((k4_orders_2 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.19/0.46        | (m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1))),
% 0.19/0.46      inference('sup-', [status(thm)], ['20', '31'])).
% 0.19/0.46  thf('33', plain,
% 0.19/0.46      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(dt_m2_orders_2, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.19/0.46         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.19/0.46         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.46       ( ![C:$i]:
% 0.19/0.46         ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.19/0.46           ( ( v6_orders_2 @ C @ A ) & 
% 0.19/0.46             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.19/0.46  thf('34', plain,
% 0.19/0.46      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.19/0.46         (~ (l1_orders_2 @ X18)
% 0.19/0.46          | ~ (v5_orders_2 @ X18)
% 0.19/0.46          | ~ (v4_orders_2 @ X18)
% 0.19/0.46          | ~ (v3_orders_2 @ X18)
% 0.19/0.46          | (v2_struct_0 @ X18)
% 0.19/0.46          | ~ (m1_orders_1 @ X19 @ (k1_orders_1 @ (u1_struct_0 @ X18)))
% 0.19/0.46          | (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.19/0.46          | ~ (m2_orders_2 @ X20 @ X18 @ X19))),
% 0.19/0.46      inference('cnf', [status(esa)], [dt_m2_orders_2])).
% 0.19/0.46  thf('35', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.19/0.46          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.46          | (v2_struct_0 @ sk_A)
% 0.19/0.46          | ~ (v3_orders_2 @ sk_A)
% 0.19/0.46          | ~ (v4_orders_2 @ sk_A)
% 0.19/0.46          | ~ (v5_orders_2 @ sk_A)
% 0.19/0.46          | ~ (l1_orders_2 @ sk_A))),
% 0.19/0.46      inference('sup-', [status(thm)], ['33', '34'])).
% 0.19/0.46  thf('36', plain, ((v3_orders_2 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('37', plain, ((v4_orders_2 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('38', plain, ((v5_orders_2 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('39', plain, ((l1_orders_2 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('40', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.19/0.46          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.46          | (v2_struct_0 @ sk_A))),
% 0.19/0.46      inference('demod', [status(thm)], ['35', '36', '37', '38', '39'])).
% 0.19/0.46  thf('41', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('42', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.46          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1))),
% 0.19/0.46      inference('clc', [status(thm)], ['40', '41'])).
% 0.19/0.46  thf('43', plain,
% 0.19/0.46      ((((k4_orders_2 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.19/0.46        | (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.46      inference('sup-', [status(thm)], ['32', '42'])).
% 0.19/0.46  thf(d16_orders_2, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.19/0.46         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.19/0.46       ( ![B:$i]:
% 0.19/0.46         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.46           ( ![C:$i]:
% 0.19/0.46             ( ( ( v6_orders_2 @ C @ A ) & 
% 0.19/0.46                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.46               ( ( m2_orders_2 @ C @ A @ B ) <=>
% 0.19/0.46                 ( ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.19/0.46                   ( r2_wellord1 @ ( u1_orders_2 @ A ) @ C ) & 
% 0.19/0.46                   ( ![D:$i]:
% 0.19/0.46                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.46                       ( ( r2_hidden @ D @ C ) =>
% 0.19/0.46                         ( ( k1_funct_1 @
% 0.19/0.46                             B @ 
% 0.19/0.46                             ( k1_orders_2 @ A @ ( k3_orders_2 @ A @ C @ D ) ) ) =
% 0.19/0.46                           ( D ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.46  thf('44', plain,
% 0.19/0.46      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.19/0.46         (~ (m1_orders_1 @ X8 @ (k1_orders_1 @ (u1_struct_0 @ X9)))
% 0.19/0.46          | ~ (m2_orders_2 @ X10 @ X9 @ X8)
% 0.19/0.46          | ((X10) != (k1_xboole_0))
% 0.19/0.46          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.19/0.46          | ~ (v6_orders_2 @ X10 @ X9)
% 0.19/0.46          | ~ (l1_orders_2 @ X9)
% 0.19/0.46          | ~ (v5_orders_2 @ X9)
% 0.19/0.46          | ~ (v4_orders_2 @ X9)
% 0.19/0.46          | ~ (v3_orders_2 @ X9)
% 0.19/0.46          | (v2_struct_0 @ X9))),
% 0.19/0.46      inference('cnf', [status(esa)], [d16_orders_2])).
% 0.19/0.46  thf('45', plain,
% 0.19/0.46      (![X8 : $i, X9 : $i]:
% 0.19/0.46         ((v2_struct_0 @ X9)
% 0.19/0.46          | ~ (v3_orders_2 @ X9)
% 0.19/0.46          | ~ (v4_orders_2 @ X9)
% 0.19/0.46          | ~ (v5_orders_2 @ X9)
% 0.19/0.46          | ~ (l1_orders_2 @ X9)
% 0.19/0.46          | ~ (v6_orders_2 @ k1_xboole_0 @ X9)
% 0.19/0.46          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.19/0.46          | ~ (m2_orders_2 @ k1_xboole_0 @ X9 @ X8)
% 0.19/0.46          | ~ (m1_orders_1 @ X8 @ (k1_orders_1 @ (u1_struct_0 @ X9))))),
% 0.19/0.46      inference('simplify', [status(thm)], ['44'])).
% 0.19/0.46  thf('46', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (((k4_orders_2 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.19/0.46          | ~ (m1_orders_1 @ X0 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.46          | ~ (m2_orders_2 @ k1_xboole_0 @ sk_A @ X0)
% 0.19/0.46          | ~ (v6_orders_2 @ k1_xboole_0 @ sk_A)
% 0.19/0.46          | ~ (l1_orders_2 @ sk_A)
% 0.19/0.46          | ~ (v5_orders_2 @ sk_A)
% 0.19/0.46          | ~ (v4_orders_2 @ sk_A)
% 0.19/0.46          | ~ (v3_orders_2 @ sk_A)
% 0.19/0.46          | (v2_struct_0 @ sk_A))),
% 0.19/0.46      inference('sup-', [status(thm)], ['43', '45'])).
% 0.19/0.46  thf('47', plain,
% 0.19/0.46      ((((k4_orders_2 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.19/0.46        | (m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1))),
% 0.19/0.46      inference('sup-', [status(thm)], ['20', '31'])).
% 0.19/0.46  thf('48', plain,
% 0.19/0.46      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('49', plain,
% 0.19/0.46      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.19/0.46         (~ (l1_orders_2 @ X18)
% 0.19/0.46          | ~ (v5_orders_2 @ X18)
% 0.19/0.46          | ~ (v4_orders_2 @ X18)
% 0.19/0.46          | ~ (v3_orders_2 @ X18)
% 0.19/0.46          | (v2_struct_0 @ X18)
% 0.19/0.46          | ~ (m1_orders_1 @ X19 @ (k1_orders_1 @ (u1_struct_0 @ X18)))
% 0.19/0.46          | (v6_orders_2 @ X20 @ X18)
% 0.19/0.46          | ~ (m2_orders_2 @ X20 @ X18 @ X19))),
% 0.19/0.46      inference('cnf', [status(esa)], [dt_m2_orders_2])).
% 0.19/0.46  thf('50', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.19/0.46          | (v6_orders_2 @ X0 @ sk_A)
% 0.19/0.46          | (v2_struct_0 @ sk_A)
% 0.19/0.46          | ~ (v3_orders_2 @ sk_A)
% 0.19/0.46          | ~ (v4_orders_2 @ sk_A)
% 0.19/0.46          | ~ (v5_orders_2 @ sk_A)
% 0.19/0.46          | ~ (l1_orders_2 @ sk_A))),
% 0.19/0.46      inference('sup-', [status(thm)], ['48', '49'])).
% 0.19/0.46  thf('51', plain, ((v3_orders_2 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('52', plain, ((v4_orders_2 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('53', plain, ((v5_orders_2 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('54', plain, ((l1_orders_2 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('55', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.19/0.46          | (v6_orders_2 @ X0 @ sk_A)
% 0.19/0.46          | (v2_struct_0 @ sk_A))),
% 0.19/0.46      inference('demod', [status(thm)], ['50', '51', '52', '53', '54'])).
% 0.19/0.46  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('57', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         ((v6_orders_2 @ X0 @ sk_A) | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1))),
% 0.19/0.46      inference('clc', [status(thm)], ['55', '56'])).
% 0.19/0.46  thf('58', plain,
% 0.19/0.46      ((((k4_orders_2 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.19/0.46        | (v6_orders_2 @ k1_xboole_0 @ sk_A))),
% 0.19/0.46      inference('sup-', [status(thm)], ['47', '57'])).
% 0.19/0.46  thf('59', plain, (~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1))),
% 0.19/0.46      inference('clc', [status(thm)], ['7', '8'])).
% 0.19/0.46  thf('60', plain,
% 0.19/0.46      ((~ (v1_xboole_0 @ k1_xboole_0) | (v6_orders_2 @ k1_xboole_0 @ sk_A))),
% 0.19/0.46      inference('sup-', [status(thm)], ['58', '59'])).
% 0.19/0.46  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.19/0.46  thf('61', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.46      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.46  thf('62', plain, ((v6_orders_2 @ k1_xboole_0 @ sk_A)),
% 0.19/0.46      inference('demod', [status(thm)], ['60', '61'])).
% 0.19/0.46  thf('63', plain, ((l1_orders_2 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('64', plain, ((v5_orders_2 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('65', plain, ((v4_orders_2 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('66', plain, ((v3_orders_2 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('67', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (((k4_orders_2 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.19/0.46          | ~ (m1_orders_1 @ X0 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.46          | ~ (m2_orders_2 @ k1_xboole_0 @ sk_A @ X0)
% 0.19/0.46          | (v2_struct_0 @ sk_A))),
% 0.19/0.46      inference('demod', [status(thm)], ['46', '62', '63', '64', '65', '66'])).
% 0.19/0.46  thf('68', plain,
% 0.19/0.46      (((v2_struct_0 @ sk_A)
% 0.19/0.46        | ~ (m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1)
% 0.19/0.46        | ((k4_orders_2 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['10', '67'])).
% 0.19/0.46  thf('69', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('70', plain,
% 0.19/0.46      ((((k4_orders_2 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.19/0.46        | ~ (m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1))),
% 0.19/0.46      inference('clc', [status(thm)], ['68', '69'])).
% 0.19/0.46  thf('71', plain,
% 0.19/0.46      ((((k4_orders_2 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.19/0.46        | (m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1))),
% 0.19/0.46      inference('sup-', [status(thm)], ['20', '31'])).
% 0.19/0.46  thf('72', plain, (((k4_orders_2 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.19/0.46      inference('clc', [status(thm)], ['70', '71'])).
% 0.19/0.46  thf('73', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.46      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.46  thf('74', plain, ($false),
% 0.19/0.46      inference('demod', [status(thm)], ['9', '72', '73'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
