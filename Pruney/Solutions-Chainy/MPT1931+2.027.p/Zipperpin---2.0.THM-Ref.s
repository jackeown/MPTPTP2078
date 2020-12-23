%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5PL7sHtZNB

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 187 expanded)
%              Number of leaves         :   35 (  72 expanded)
%              Depth                    :   23
%              Number of atoms          :  662 (1938 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(r2_waybel_0_type,type,(
    r2_waybel_0: $i > $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(rc2_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v1_xboole_0 @ B )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( v1_xboole_0 @ ( sk_B_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('1',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t29_yellow_6,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_struct_0 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v4_orders_2 @ B )
              & ( v7_waybel_0 @ B )
              & ( l1_waybel_0 @ B @ A ) )
           => ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_yellow_6])).

thf('2',plain,(
    l1_waybel_0 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( r2_waybel_0 @ A @ B @ C )
            <=> ~ ( r1_waybel_0 @ A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) )).

thf('3',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( l1_waybel_0 @ X22 @ X23 )
      | ( r1_waybel_0 @ X23 @ X22 @ ( k6_subset_1 @ ( u1_struct_0 @ X23 ) @ X24 ) )
      | ( r2_waybel_0 @ X23 @ X22 @ X24 )
      | ~ ( l1_struct_0 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t10_waybel_0])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k6_subset_1 @ X7 @ X8 )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('5',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( l1_waybel_0 @ X22 @ X23 )
      | ( r1_waybel_0 @ X23 @ X22 @ ( k4_xboole_0 @ ( u1_struct_0 @ X23 ) @ X24 ) )
      | ( r2_waybel_0 @ X23 @ X22 @ X24 )
      | ~ ( l1_struct_0 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B_2 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B_2 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_waybel_0 @ sk_A @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_2 )
    | ( r2_waybel_0 @ sk_A @ sk_B_2 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','8'])).

thf('10',plain,(
    ~ ( r1_waybel_0 @ sk_A @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_waybel_0 @ sk_A @ sk_B_2 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ( r2_waybel_0 @ sk_A @ sk_B_2 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    r2_waybel_0 @ sk_A @ sk_B_2 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['13','14'])).

thf(t8_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i,D: $i] :
              ( ( r1_tarski @ C @ D )
             => ( ( ( r1_waybel_0 @ A @ B @ C )
                 => ( r1_waybel_0 @ A @ B @ D ) )
                & ( ( r2_waybel_0 @ A @ B @ C )
                 => ( r2_waybel_0 @ A @ B @ D ) ) ) ) ) ) )).

thf('16',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( l1_waybel_0 @ X26 @ X27 )
      | ~ ( r2_waybel_0 @ X27 @ X26 @ X28 )
      | ( r2_waybel_0 @ X27 @ X26 @ X29 )
      | ~ ( r1_tarski @ X28 @ X29 )
      | ~ ( l1_struct_0 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t8_waybel_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ~ ( l1_waybel_0 @ sk_B_2 @ sk_A )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X6: $i] :
      ( v1_xboole_0 @ ( sk_B_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('20',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('21',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('22',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,(
    l1_waybel_0 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X0 )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['17','18','25','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ( r2_waybel_0 @ sk_A @ sk_B_2 @ X0 ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( r2_waybel_0 @ sk_A @ sk_B_2 @ X0 ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r2_waybel_0 @ sk_A @ sk_B_2 @ X0 ) ),
    inference(clc,[status(thm)],['29','30'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('33',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ ( sk_B @ X5 ) @ X5 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(d12_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( r2_waybel_0 @ A @ B @ C )
            <=> ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) )
                 => ? [E: $i] :
                      ( ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C )
                      & ( r1_orders_2 @ B @ D @ E )
                      & ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) ) ) ) )).

thf('34',plain,(
    ! [X16: $i,X17: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( l1_waybel_0 @ X16 @ X17 )
      | ~ ( r2_waybel_0 @ X17 @ X16 @ X20 )
      | ( m1_subset_1 @ ( sk_E @ X21 @ X20 @ X16 @ X17 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X2 @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_waybel_0 @ X1 @ X0 @ X2 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ~ ( l1_waybel_0 @ sk_B_2 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_2 ) ) @ X0 @ sk_B_2 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    l1_waybel_0 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_2 ) ) @ X0 @ sk_B_2 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_2 ) ) @ X0 @ sk_B_2 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_2 ) ) @ X0 @ sk_B_2 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X16: $i,X17: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( l1_waybel_0 @ X16 @ X17 )
      | ~ ( r2_waybel_0 @ X17 @ X16 @ X20 )
      | ( r2_hidden @ ( k2_waybel_0 @ X17 @ X16 @ ( sk_E @ X21 @ X20 @ X16 @ X17 ) ) @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ sk_B_2 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_2 ) ) @ X0 @ sk_B_2 @ sk_A ) @ X2 @ sk_B_2 @ X1 ) ) @ X2 )
      | ~ ( r2_waybel_0 @ X1 @ sk_B_2 @ X2 )
      | ~ ( l1_waybel_0 @ sk_B_2 @ X1 )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ~ ( l1_waybel_0 @ sk_B_2 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_2 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_2 ) ) @ X1 @ sk_B_2 @ sk_A ) @ X0 @ sk_B_2 @ sk_A ) ) @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','45'])).

thf('47',plain,(
    l1_waybel_0 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_2 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_2 ) ) @ X1 @ sk_B_2 @ sk_A ) @ X0 @ sk_B_2 @ sk_A ) ) @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_2 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_2 ) ) @ X1 @ sk_B_2 @ sk_A ) @ X0 @ sk_B_2 @ sk_A ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_2 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_2 ) ) @ X1 @ sk_B_2 @ sk_A ) @ X0 @ sk_B_2 @ sk_A ) ) @ X0 ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('55',plain,(
    ! [X1: $i] :
      ~ ( v1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5PL7sHtZNB
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:46:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 69 iterations in 0.034s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.21/0.47  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.21/0.47  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.47  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.47  thf(k2_waybel_0_type, type, k2_waybel_0: $i > $i > $i > $i).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.47  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.47  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.21/0.47  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.21/0.47  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.21/0.47  thf(r2_waybel_0_type, type, r2_waybel_0: $i > $i > $i > $o).
% 0.21/0.47  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.21/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(rc2_subset_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ?[B:$i]:
% 0.21/0.47       ( ( v1_xboole_0 @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.21/0.47  thf('0', plain, (![X6 : $i]: (v1_xboole_0 @ (sk_B_1 @ X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [rc2_subset_1])).
% 0.21/0.47  thf(t3_boole, axiom,
% 0.21/0.47    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.47  thf('1', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.21/0.47      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.47  thf(t29_yellow_6, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.47             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.47           ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.47          ( ![B:$i]:
% 0.21/0.47            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.21/0.47                ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.47              ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t29_yellow_6])).
% 0.21/0.47  thf('2', plain, ((l1_waybel_0 @ sk_B_2 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t10_waybel_0, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.47           ( ![C:$i]:
% 0.21/0.47             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 0.21/0.47               ( ~( r1_waybel_0 @
% 0.21/0.47                    A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ))).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.47         ((v2_struct_0 @ X22)
% 0.21/0.47          | ~ (l1_waybel_0 @ X22 @ X23)
% 0.21/0.47          | (r1_waybel_0 @ X23 @ X22 @ 
% 0.21/0.47             (k6_subset_1 @ (u1_struct_0 @ X23) @ X24))
% 0.21/0.47          | (r2_waybel_0 @ X23 @ X22 @ X24)
% 0.21/0.47          | ~ (l1_struct_0 @ X23)
% 0.21/0.47          | (v2_struct_0 @ X23))),
% 0.21/0.47      inference('cnf', [status(esa)], [t10_waybel_0])).
% 0.21/0.47  thf(redefinition_k6_subset_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X7 : $i, X8 : $i]: ((k6_subset_1 @ X7 @ X8) = (k4_xboole_0 @ X7 @ X8))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.47         ((v2_struct_0 @ X22)
% 0.21/0.47          | ~ (l1_waybel_0 @ X22 @ X23)
% 0.21/0.47          | (r1_waybel_0 @ X23 @ X22 @ 
% 0.21/0.47             (k4_xboole_0 @ (u1_struct_0 @ X23) @ X24))
% 0.21/0.47          | (r2_waybel_0 @ X23 @ X22 @ X24)
% 0.21/0.47          | ~ (l1_struct_0 @ X23)
% 0.21/0.47          | (v2_struct_0 @ X23))),
% 0.21/0.47      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((v2_struct_0 @ sk_A)
% 0.21/0.47          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.47          | (r2_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.21/0.47          | (r1_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.21/0.47             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))
% 0.21/0.47          | (v2_struct_0 @ sk_B_2))),
% 0.21/0.47      inference('sup-', [status(thm)], ['2', '5'])).
% 0.21/0.47  thf('7', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((v2_struct_0 @ sk_A)
% 0.21/0.47          | (r2_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.21/0.47          | (r1_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.21/0.47             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))
% 0.21/0.47          | (v2_struct_0 @ sk_B_2))),
% 0.21/0.47      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (((r1_waybel_0 @ sk_A @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.21/0.47        | (v2_struct_0 @ sk_B_2)
% 0.21/0.47        | (r2_waybel_0 @ sk_A @ sk_B_2 @ k1_xboole_0)
% 0.21/0.47        | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('sup+', [status(thm)], ['1', '8'])).
% 0.21/0.47  thf('10', plain, (~ (r1_waybel_0 @ sk_A @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (((v2_struct_0 @ sk_A)
% 0.21/0.47        | (r2_waybel_0 @ sk_A @ sk_B_2 @ k1_xboole_0)
% 0.21/0.47        | (v2_struct_0 @ sk_B_2))),
% 0.21/0.47      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.47  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (((v2_struct_0 @ sk_B_2) | (r2_waybel_0 @ sk_A @ sk_B_2 @ k1_xboole_0))),
% 0.21/0.47      inference('clc', [status(thm)], ['11', '12'])).
% 0.21/0.47  thf('14', plain, (~ (v2_struct_0 @ sk_B_2)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('15', plain, ((r2_waybel_0 @ sk_A @ sk_B_2 @ k1_xboole_0)),
% 0.21/0.47      inference('clc', [status(thm)], ['13', '14'])).
% 0.21/0.47  thf(t8_waybel_0, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.47           ( ![C:$i,D:$i]:
% 0.21/0.47             ( ( r1_tarski @ C @ D ) =>
% 0.21/0.47               ( ( ( r1_waybel_0 @ A @ B @ C ) => ( r1_waybel_0 @ A @ B @ D ) ) & 
% 0.21/0.47                 ( ( r2_waybel_0 @ A @ B @ C ) => ( r2_waybel_0 @ A @ B @ D ) ) ) ) ) ) ) ))).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.21/0.47         ((v2_struct_0 @ X26)
% 0.21/0.47          | ~ (l1_waybel_0 @ X26 @ X27)
% 0.21/0.47          | ~ (r2_waybel_0 @ X27 @ X26 @ X28)
% 0.21/0.47          | (r2_waybel_0 @ X27 @ X26 @ X29)
% 0.21/0.47          | ~ (r1_tarski @ X28 @ X29)
% 0.21/0.47          | ~ (l1_struct_0 @ X27)
% 0.21/0.47          | (v2_struct_0 @ X27))),
% 0.21/0.47      inference('cnf', [status(esa)], [t8_waybel_0])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((v2_struct_0 @ sk_A)
% 0.21/0.47          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.47          | ~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.21/0.47          | (r2_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.21/0.47          | ~ (l1_waybel_0 @ sk_B_2 @ sk_A)
% 0.21/0.47          | (v2_struct_0 @ sk_B_2))),
% 0.21/0.47      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.47  thf('18', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('19', plain, (![X6 : $i]: (v1_xboole_0 @ (sk_B_1 @ X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [rc2_subset_1])).
% 0.21/0.47  thf(d3_tarski, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      (![X1 : $i, X3 : $i]:
% 0.21/0.47         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.47      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.47  thf(t4_subset_1, axiom,
% 0.21/0.47    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.47  thf('21', plain,
% 0.21/0.47      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.21/0.47      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.47  thf(t5_subset, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.21/0.47          ( v1_xboole_0 @ C ) ) ))).
% 0.21/0.47  thf('22', plain,
% 0.21/0.47      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X13 @ X14)
% 0.21/0.47          | ~ (v1_xboole_0 @ X15)
% 0.21/0.47          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t5_subset])).
% 0.21/0.47  thf('23', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.47  thf('24', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((r1_tarski @ k1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['20', '23'])).
% 0.21/0.47  thf('25', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.21/0.47      inference('sup-', [status(thm)], ['19', '24'])).
% 0.21/0.47  thf('26', plain, ((l1_waybel_0 @ sk_B_2 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('27', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((v2_struct_0 @ sk_A)
% 0.21/0.47          | (r2_waybel_0 @ sk_A @ sk_B_2 @ X0)
% 0.21/0.47          | (v2_struct_0 @ sk_B_2))),
% 0.21/0.47      inference('demod', [status(thm)], ['17', '18', '25', '26'])).
% 0.21/0.47  thf('28', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('29', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((v2_struct_0 @ sk_B_2) | (r2_waybel_0 @ sk_A @ sk_B_2 @ X0))),
% 0.21/0.47      inference('clc', [status(thm)], ['27', '28'])).
% 0.21/0.47  thf('30', plain, (~ (v2_struct_0 @ sk_B_2)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('31', plain, (![X0 : $i]: (r2_waybel_0 @ sk_A @ sk_B_2 @ X0)),
% 0.21/0.47      inference('clc', [status(thm)], ['29', '30'])).
% 0.21/0.47  thf('32', plain, (![X0 : $i]: (r2_waybel_0 @ sk_A @ sk_B_2 @ X0)),
% 0.21/0.47      inference('clc', [status(thm)], ['29', '30'])).
% 0.21/0.47  thf(existence_m1_subset_1, axiom,
% 0.21/0.47    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.21/0.47  thf('33', plain, (![X5 : $i]: (m1_subset_1 @ (sk_B @ X5) @ X5)),
% 0.21/0.47      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.21/0.47  thf(d12_waybel_0, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.47           ( ![C:$i]:
% 0.21/0.47             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 0.21/0.47               ( ![D:$i]:
% 0.21/0.47                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.47                   ( ?[E:$i]:
% 0.21/0.47                     ( ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) & 
% 0.21/0.47                       ( r1_orders_2 @ B @ D @ E ) & 
% 0.21/0.47                       ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.47  thf('34', plain,
% 0.21/0.47      (![X16 : $i, X17 : $i, X20 : $i, X21 : $i]:
% 0.21/0.47         ((v2_struct_0 @ X16)
% 0.21/0.47          | ~ (l1_waybel_0 @ X16 @ X17)
% 0.21/0.47          | ~ (r2_waybel_0 @ X17 @ X16 @ X20)
% 0.21/0.47          | (m1_subset_1 @ (sk_E @ X21 @ X20 @ X16 @ X17) @ (u1_struct_0 @ X16))
% 0.21/0.47          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X16))
% 0.21/0.47          | ~ (l1_struct_0 @ X17)
% 0.21/0.47          | (v2_struct_0 @ X17))),
% 0.21/0.47      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.21/0.47  thf('35', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         ((v2_struct_0 @ X1)
% 0.21/0.47          | ~ (l1_struct_0 @ X1)
% 0.21/0.47          | (m1_subset_1 @ 
% 0.21/0.47             (sk_E @ (sk_B @ (u1_struct_0 @ X0)) @ X2 @ X0 @ X1) @ 
% 0.21/0.47             (u1_struct_0 @ X0))
% 0.21/0.47          | ~ (r2_waybel_0 @ X1 @ X0 @ X2)
% 0.21/0.47          | ~ (l1_waybel_0 @ X0 @ X1)
% 0.21/0.47          | (v2_struct_0 @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.47  thf('36', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((v2_struct_0 @ sk_B_2)
% 0.21/0.47          | ~ (l1_waybel_0 @ sk_B_2 @ sk_A)
% 0.21/0.47          | (m1_subset_1 @ 
% 0.21/0.47             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_2)) @ X0 @ sk_B_2 @ sk_A) @ 
% 0.21/0.47             (u1_struct_0 @ sk_B_2))
% 0.21/0.47          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.47          | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['32', '35'])).
% 0.21/0.47  thf('37', plain, ((l1_waybel_0 @ sk_B_2 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('38', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('39', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((v2_struct_0 @ sk_B_2)
% 0.21/0.47          | (m1_subset_1 @ 
% 0.21/0.47             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_2)) @ X0 @ sk_B_2 @ sk_A) @ 
% 0.21/0.47             (u1_struct_0 @ sk_B_2))
% 0.21/0.47          | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.21/0.47  thf('40', plain, (~ (v2_struct_0 @ sk_B_2)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('41', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((v2_struct_0 @ sk_A)
% 0.21/0.47          | (m1_subset_1 @ 
% 0.21/0.47             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_2)) @ X0 @ sk_B_2 @ sk_A) @ 
% 0.21/0.47             (u1_struct_0 @ sk_B_2)))),
% 0.21/0.47      inference('clc', [status(thm)], ['39', '40'])).
% 0.21/0.47  thf('42', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('43', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (m1_subset_1 @ 
% 0.21/0.47          (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_2)) @ X0 @ sk_B_2 @ sk_A) @ 
% 0.21/0.47          (u1_struct_0 @ sk_B_2))),
% 0.21/0.47      inference('clc', [status(thm)], ['41', '42'])).
% 0.21/0.47  thf('44', plain,
% 0.21/0.47      (![X16 : $i, X17 : $i, X20 : $i, X21 : $i]:
% 0.21/0.47         ((v2_struct_0 @ X16)
% 0.21/0.47          | ~ (l1_waybel_0 @ X16 @ X17)
% 0.21/0.47          | ~ (r2_waybel_0 @ X17 @ X16 @ X20)
% 0.21/0.47          | (r2_hidden @ 
% 0.21/0.47             (k2_waybel_0 @ X17 @ X16 @ (sk_E @ X21 @ X20 @ X16 @ X17)) @ X20)
% 0.21/0.47          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X16))
% 0.21/0.47          | ~ (l1_struct_0 @ X17)
% 0.21/0.47          | (v2_struct_0 @ X17))),
% 0.21/0.47      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.21/0.47  thf('45', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         ((v2_struct_0 @ X1)
% 0.21/0.47          | ~ (l1_struct_0 @ X1)
% 0.21/0.47          | (r2_hidden @ 
% 0.21/0.47             (k2_waybel_0 @ X1 @ sk_B_2 @ 
% 0.21/0.47              (sk_E @ 
% 0.21/0.47               (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_2)) @ X0 @ sk_B_2 @ sk_A) @ 
% 0.21/0.47               X2 @ sk_B_2 @ X1)) @ 
% 0.21/0.47             X2)
% 0.21/0.47          | ~ (r2_waybel_0 @ X1 @ sk_B_2 @ X2)
% 0.21/0.47          | ~ (l1_waybel_0 @ sk_B_2 @ X1)
% 0.21/0.47          | (v2_struct_0 @ sk_B_2))),
% 0.21/0.47      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.47  thf('46', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((v2_struct_0 @ sk_B_2)
% 0.21/0.47          | ~ (l1_waybel_0 @ sk_B_2 @ sk_A)
% 0.21/0.47          | (r2_hidden @ 
% 0.21/0.47             (k2_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.21/0.47              (sk_E @ 
% 0.21/0.47               (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_2)) @ X1 @ sk_B_2 @ sk_A) @ 
% 0.21/0.47               X0 @ sk_B_2 @ sk_A)) @ 
% 0.21/0.47             X0)
% 0.21/0.47          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.47          | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['31', '45'])).
% 0.21/0.47  thf('47', plain, ((l1_waybel_0 @ sk_B_2 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('48', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('49', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((v2_struct_0 @ sk_B_2)
% 0.21/0.47          | (r2_hidden @ 
% 0.21/0.47             (k2_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.21/0.47              (sk_E @ 
% 0.21/0.47               (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_2)) @ X1 @ sk_B_2 @ sk_A) @ 
% 0.21/0.47               X0 @ sk_B_2 @ sk_A)) @ 
% 0.21/0.47             X0)
% 0.21/0.47          | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.21/0.47  thf('50', plain, (~ (v2_struct_0 @ sk_B_2)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('51', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((v2_struct_0 @ sk_A)
% 0.21/0.47          | (r2_hidden @ 
% 0.21/0.47             (k2_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.21/0.47              (sk_E @ 
% 0.21/0.47               (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_2)) @ X1 @ sk_B_2 @ sk_A) @ 
% 0.21/0.47               X0 @ sk_B_2 @ sk_A)) @ 
% 0.21/0.47             X0))),
% 0.21/0.47      inference('clc', [status(thm)], ['49', '50'])).
% 0.21/0.47  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('53', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (r2_hidden @ 
% 0.21/0.47          (k2_waybel_0 @ sk_A @ sk_B_2 @ 
% 0.21/0.47           (sk_E @ 
% 0.21/0.47            (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_2)) @ X1 @ sk_B_2 @ sk_A) @ 
% 0.21/0.47            X0 @ sk_B_2 @ sk_A)) @ 
% 0.21/0.47          X0)),
% 0.21/0.47      inference('clc', [status(thm)], ['51', '52'])).
% 0.21/0.47  thf('54', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.47  thf('55', plain, (![X1 : $i]: ~ (v1_xboole_0 @ X1)),
% 0.21/0.47      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.47  thf('56', plain, ($false), inference('sup-', [status(thm)], ['0', '55'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
