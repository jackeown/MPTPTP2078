%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hgqowt8GxS

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:35 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 151 expanded)
%              Number of leaves         :   27 (  55 expanded)
%              Depth                    :   22
%              Number of atoms          :  776 (2183 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r8_relat_2_type,type,(
    r8_relat_2: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(t26_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ( v4_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( ( r1_orders_2 @ A @ B @ C )
                      & ( r1_orders_2 @ A @ C @ D ) )
                   => ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v4_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( ( r1_orders_2 @ A @ B @ C )
                        & ( r1_orders_2 @ A @ C @ D ) )
                     => ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t26_orders_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_orders_2 @ A @ B @ C )
              <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( r1_orders_2 @ X21 @ X20 @ X22 )
      | ( r2_hidden @ ( k4_tarski @ X20 @ X22 ) @ ( u1_orders_2 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_orders_2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B_1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B_1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B_1 @ sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_B_1 @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    r1_orders_2 @ sk_A @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r2_hidden @ ( k4_tarski @ sk_B_1 @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

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
    ~ ( v1_xboole_0 @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('13',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d5_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v4_orders_2 @ A )
      <=> ( r8_relat_2 @ ( u1_orders_2 @ A ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('17',plain,(
    ! [X19: $i] :
      ( ~ ( v4_orders_2 @ X19 )
      | ( r8_relat_2 @ ( u1_orders_2 @ X19 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d5_orders_2])).

thf('18',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( r1_orders_2 @ X21 @ X20 @ X22 )
      | ( r2_hidden @ ( k4_tarski @ X20 @ X22 ) @ ( u1_orders_2 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_orders_2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_D_1 ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,(
    r1_orders_2 @ sk_A @ sk_C_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_D_1 ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('27',plain,(
    ! [X23: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( l1_orders_2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('28',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('30',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    r2_hidden @ ( k4_tarski @ sk_B_1 @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(d8_relat_2,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r8_relat_2 @ A @ B )
        <=> ! [C: $i,D: $i,E: $i] :
              ( ( ( r2_hidden @ C @ B )
                & ( r2_hidden @ D @ B )
                & ( r2_hidden @ E @ B )
                & ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
                & ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) )
             => ( r2_hidden @ ( k4_tarski @ C @ E ) @ A ) ) ) ) )).

thf('33',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r8_relat_2 @ X14 @ X15 )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X17 ) @ X14 )
      | ~ ( r2_hidden @ X17 @ X15 )
      | ~ ( r2_hidden @ X16 @ X15 )
      | ~ ( r2_hidden @ X18 @ X15 )
      | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X18 ) @ X14 )
      | ( r2_hidden @ ( k4_tarski @ X16 @ X18 ) @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_2])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B_1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ sk_B_1 @ X1 )
      | ~ ( r2_hidden @ sk_C_1 @ X1 )
      | ~ ( r8_relat_2 @ ( u1_orders_2 @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( r8_relat_2 @ ( u1_orders_2 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_B_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X1 ) @ ( u1_orders_2 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B_1 @ X1 ) @ ( u1_orders_2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r8_relat_2 @ ( u1_orders_2 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_B_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X1 ) @ ( u1_orders_2 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B_1 @ X1 ) @ ( u1_orders_2 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ sk_B_1 @ sk_D_1 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r2_hidden @ sk_D_1 @ X0 )
      | ~ ( r2_hidden @ sk_B_1 @ X0 )
      | ~ ( r2_hidden @ sk_C_1 @ X0 )
      | ~ ( r8_relat_2 @ ( u1_orders_2 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','37'])).

thf('39',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_B_1 @ sk_D_1 ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','38'])).

thf('40',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_B_1 @ sk_D_1 ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_B_1 @ sk_D_1 ) @ ( u1_orders_2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','42'])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_B_1 @ sk_D_1 ) @ ( u1_orders_2 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','43'])).

thf('45',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B_1 @ sk_D_1 ) @ ( u1_orders_2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('48',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_B_1 @ sk_D_1 ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference(clc,[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X20 @ X22 ) @ ( u1_orders_2 @ X21 ) )
      | ( r1_orders_2 @ X21 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_orders_2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('51',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_B_1 @ sk_D_1 )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_B_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['51','52','53','54'])).

thf('56',plain,(
    ~ ( r1_orders_2 @ sk_A @ sk_B_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X23: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( l1_orders_2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('59',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X10 ) ) )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_xboole_0 @ ( u1_orders_2 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( v1_xboole_0 @ ( u1_orders_2 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_xboole_0 @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    $false ),
    inference(demod,[status(thm)],['10','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hgqowt8GxS
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:35:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 152 iterations in 0.066s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.52  thf(r8_relat_2_type, type, r8_relat_2: $i > $i > $o).
% 0.22/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.52  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.22/0.52  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.22/0.52  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.22/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.52  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.22/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.52  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.22/0.52  thf(t26_orders_2, conjecture,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( v4_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.52           ( ![C:$i]:
% 0.22/0.52             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.52               ( ![D:$i]:
% 0.22/0.52                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.52                   ( ( ( r1_orders_2 @ A @ B @ C ) & 
% 0.22/0.52                       ( r1_orders_2 @ A @ C @ D ) ) =>
% 0.22/0.52                     ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i]:
% 0.22/0.52        ( ( ( v4_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.22/0.52          ( ![B:$i]:
% 0.22/0.52            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.52              ( ![C:$i]:
% 0.22/0.52                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.52                  ( ![D:$i]:
% 0.22/0.52                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.52                      ( ( ( r1_orders_2 @ A @ B @ C ) & 
% 0.22/0.52                          ( r1_orders_2 @ A @ C @ D ) ) =>
% 0.22/0.52                        ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t26_orders_2])).
% 0.22/0.52  thf('0', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('1', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(d9_orders_2, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( l1_orders_2 @ A ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.52           ( ![C:$i]:
% 0.22/0.52             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.52               ( ( r1_orders_2 @ A @ B @ C ) <=>
% 0.22/0.52                 ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) ) ))).
% 0.22/0.52  thf('2', plain,
% 0.22/0.52      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.22/0.52          | ~ (r1_orders_2 @ X21 @ X20 @ X22)
% 0.22/0.52          | (r2_hidden @ (k4_tarski @ X20 @ X22) @ (u1_orders_2 @ X21))
% 0.22/0.52          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.22/0.52          | ~ (l1_orders_2 @ X21))),
% 0.22/0.52      inference('cnf', [status(esa)], [d9_orders_2])).
% 0.22/0.52  thf('3', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (l1_orders_2 @ sk_A)
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.52          | (r2_hidden @ (k4_tarski @ sk_B_1 @ X0) @ (u1_orders_2 @ sk_A))
% 0.22/0.52          | ~ (r1_orders_2 @ sk_A @ sk_B_1 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.52  thf('4', plain, ((l1_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('5', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.52          | (r2_hidden @ (k4_tarski @ sk_B_1 @ X0) @ (u1_orders_2 @ sk_A))
% 0.22/0.52          | ~ (r1_orders_2 @ sk_A @ sk_B_1 @ X0))),
% 0.22/0.52      inference('demod', [status(thm)], ['3', '4'])).
% 0.22/0.52  thf('6', plain,
% 0.22/0.52      ((~ (r1_orders_2 @ sk_A @ sk_B_1 @ sk_C_1)
% 0.22/0.52        | (r2_hidden @ (k4_tarski @ sk_B_1 @ sk_C_1) @ (u1_orders_2 @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['0', '5'])).
% 0.22/0.52  thf('7', plain, ((r1_orders_2 @ sk_A @ sk_B_1 @ sk_C_1)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      ((r2_hidden @ (k4_tarski @ sk_B_1 @ sk_C_1) @ (u1_orders_2 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['6', '7'])).
% 0.22/0.52  thf(d1_xboole_0, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.52  thf('9', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.22/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.52  thf('10', plain, (~ (v1_xboole_0 @ (u1_orders_2 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.52  thf('11', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(d2_subset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( v1_xboole_0 @ A ) =>
% 0.22/0.52         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.22/0.52       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.52         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.52  thf('12', plain,
% 0.22/0.52      (![X3 : $i, X4 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X3 @ X4)
% 0.22/0.52          | (r2_hidden @ X3 @ X4)
% 0.22/0.52          | (v1_xboole_0 @ X4))),
% 0.22/0.52      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.52        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.52  thf('14', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      (![X3 : $i, X4 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X3 @ X4)
% 0.22/0.52          | (r2_hidden @ X3 @ X4)
% 0.22/0.52          | (v1_xboole_0 @ X4))),
% 0.22/0.52      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.52        | (r2_hidden @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.52  thf(d5_orders_2, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( l1_orders_2 @ A ) =>
% 0.22/0.52       ( ( v4_orders_2 @ A ) <=>
% 0.22/0.52         ( r8_relat_2 @ ( u1_orders_2 @ A ) @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.52  thf('17', plain,
% 0.22/0.52      (![X19 : $i]:
% 0.22/0.52         (~ (v4_orders_2 @ X19)
% 0.22/0.52          | (r8_relat_2 @ (u1_orders_2 @ X19) @ (u1_struct_0 @ X19))
% 0.22/0.52          | ~ (l1_orders_2 @ X19))),
% 0.22/0.52      inference('cnf', [status(esa)], [d5_orders_2])).
% 0.22/0.52  thf('18', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('19', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('20', plain,
% 0.22/0.52      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.22/0.52          | ~ (r1_orders_2 @ X21 @ X20 @ X22)
% 0.22/0.52          | (r2_hidden @ (k4_tarski @ X20 @ X22) @ (u1_orders_2 @ X21))
% 0.22/0.52          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.22/0.52          | ~ (l1_orders_2 @ X21))),
% 0.22/0.52      inference('cnf', [status(esa)], [d9_orders_2])).
% 0.22/0.52  thf('21', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (l1_orders_2 @ sk_A)
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.52          | (r2_hidden @ (k4_tarski @ sk_C_1 @ X0) @ (u1_orders_2 @ sk_A))
% 0.22/0.52          | ~ (r1_orders_2 @ sk_A @ sk_C_1 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.52  thf('22', plain, ((l1_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.52          | (r2_hidden @ (k4_tarski @ sk_C_1 @ X0) @ (u1_orders_2 @ sk_A))
% 0.22/0.52          | ~ (r1_orders_2 @ sk_A @ sk_C_1 @ X0))),
% 0.22/0.52      inference('demod', [status(thm)], ['21', '22'])).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      ((~ (r1_orders_2 @ sk_A @ sk_C_1 @ sk_D_1)
% 0.22/0.52        | (r2_hidden @ (k4_tarski @ sk_C_1 @ sk_D_1) @ (u1_orders_2 @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['18', '23'])).
% 0.22/0.52  thf('25', plain, ((r1_orders_2 @ sk_A @ sk_C_1 @ sk_D_1)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('26', plain,
% 0.22/0.52      ((r2_hidden @ (k4_tarski @ sk_C_1 @ sk_D_1) @ (u1_orders_2 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['24', '25'])).
% 0.22/0.52  thf(dt_u1_orders_2, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( l1_orders_2 @ A ) =>
% 0.22/0.52       ( m1_subset_1 @
% 0.22/0.52         ( u1_orders_2 @ A ) @ 
% 0.22/0.52         ( k1_zfmisc_1 @
% 0.22/0.52           ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.22/0.52  thf('27', plain,
% 0.22/0.52      (![X23 : $i]:
% 0.22/0.52         ((m1_subset_1 @ (u1_orders_2 @ X23) @ 
% 0.22/0.52           (k1_zfmisc_1 @ 
% 0.22/0.52            (k2_zfmisc_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X23))))
% 0.22/0.52          | ~ (l1_orders_2 @ X23))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.22/0.52  thf(cc2_relat_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ A ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.22/0.52  thf('28', plain,
% 0.22/0.52      (![X6 : $i, X7 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.22/0.52          | (v1_relat_1 @ X6)
% 0.22/0.52          | ~ (v1_relat_1 @ X7))),
% 0.22/0.52      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.22/0.52  thf('29', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (l1_orders_2 @ X0)
% 0.22/0.52          | ~ (v1_relat_1 @ 
% 0.22/0.52               (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))
% 0.22/0.52          | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.52  thf(fc6_relat_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.22/0.52  thf('30', plain,
% 0.22/0.52      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.22/0.52      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.22/0.52  thf('31', plain,
% 0.22/0.52      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 0.22/0.52      inference('demod', [status(thm)], ['29', '30'])).
% 0.22/0.52  thf('32', plain,
% 0.22/0.52      ((r2_hidden @ (k4_tarski @ sk_B_1 @ sk_C_1) @ (u1_orders_2 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['6', '7'])).
% 0.22/0.52  thf(d8_relat_2, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ A ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( r8_relat_2 @ A @ B ) <=>
% 0.22/0.52           ( ![C:$i,D:$i,E:$i]:
% 0.22/0.52             ( ( ( r2_hidden @ C @ B ) & ( r2_hidden @ D @ B ) & 
% 0.22/0.52                 ( r2_hidden @ E @ B ) & 
% 0.22/0.52                 ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) & 
% 0.22/0.52                 ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) =>
% 0.22/0.52               ( r2_hidden @ ( k4_tarski @ C @ E ) @ A ) ) ) ) ) ))).
% 0.22/0.52  thf('33', plain,
% 0.22/0.52      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.52         (~ (r8_relat_2 @ X14 @ X15)
% 0.22/0.52          | ~ (r2_hidden @ (k4_tarski @ X16 @ X17) @ X14)
% 0.22/0.52          | ~ (r2_hidden @ X17 @ X15)
% 0.22/0.52          | ~ (r2_hidden @ X16 @ X15)
% 0.22/0.52          | ~ (r2_hidden @ X18 @ X15)
% 0.22/0.52          | ~ (r2_hidden @ (k4_tarski @ X17 @ X18) @ X14)
% 0.22/0.52          | (r2_hidden @ (k4_tarski @ X16 @ X18) @ X14)
% 0.22/0.52          | ~ (v1_relat_1 @ X14))),
% 0.22/0.52      inference('cnf', [status(esa)], [d8_relat_2])).
% 0.22/0.52  thf('34', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (~ (v1_relat_1 @ (u1_orders_2 @ sk_A))
% 0.22/0.52          | (r2_hidden @ (k4_tarski @ sk_B_1 @ X0) @ (u1_orders_2 @ sk_A))
% 0.22/0.52          | ~ (r2_hidden @ (k4_tarski @ sk_C_1 @ X0) @ (u1_orders_2 @ sk_A))
% 0.22/0.52          | ~ (r2_hidden @ X0 @ X1)
% 0.22/0.52          | ~ (r2_hidden @ sk_B_1 @ X1)
% 0.22/0.52          | ~ (r2_hidden @ sk_C_1 @ X1)
% 0.22/0.52          | ~ (r8_relat_2 @ (u1_orders_2 @ sk_A) @ X1))),
% 0.22/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.52  thf('35', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (~ (l1_orders_2 @ sk_A)
% 0.22/0.52          | ~ (r8_relat_2 @ (u1_orders_2 @ sk_A) @ X0)
% 0.22/0.52          | ~ (r2_hidden @ sk_C_1 @ X0)
% 0.22/0.52          | ~ (r2_hidden @ sk_B_1 @ X0)
% 0.22/0.52          | ~ (r2_hidden @ X1 @ X0)
% 0.22/0.52          | ~ (r2_hidden @ (k4_tarski @ sk_C_1 @ X1) @ (u1_orders_2 @ sk_A))
% 0.22/0.52          | (r2_hidden @ (k4_tarski @ sk_B_1 @ X1) @ (u1_orders_2 @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['31', '34'])).
% 0.22/0.52  thf('36', plain, ((l1_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('37', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (~ (r8_relat_2 @ (u1_orders_2 @ sk_A) @ X0)
% 0.22/0.52          | ~ (r2_hidden @ sk_C_1 @ X0)
% 0.22/0.52          | ~ (r2_hidden @ sk_B_1 @ X0)
% 0.22/0.52          | ~ (r2_hidden @ X1 @ X0)
% 0.22/0.52          | ~ (r2_hidden @ (k4_tarski @ sk_C_1 @ X1) @ (u1_orders_2 @ sk_A))
% 0.22/0.52          | (r2_hidden @ (k4_tarski @ sk_B_1 @ X1) @ (u1_orders_2 @ sk_A)))),
% 0.22/0.52      inference('demod', [status(thm)], ['35', '36'])).
% 0.22/0.52  thf('38', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((r2_hidden @ (k4_tarski @ sk_B_1 @ sk_D_1) @ (u1_orders_2 @ sk_A))
% 0.22/0.52          | ~ (r2_hidden @ sk_D_1 @ X0)
% 0.22/0.52          | ~ (r2_hidden @ sk_B_1 @ X0)
% 0.22/0.52          | ~ (r2_hidden @ sk_C_1 @ X0)
% 0.22/0.52          | ~ (r8_relat_2 @ (u1_orders_2 @ sk_A) @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['26', '37'])).
% 0.22/0.52  thf('39', plain,
% 0.22/0.52      ((~ (l1_orders_2 @ sk_A)
% 0.22/0.52        | ~ (v4_orders_2 @ sk_A)
% 0.22/0.52        | ~ (r2_hidden @ sk_C_1 @ (u1_struct_0 @ sk_A))
% 0.22/0.52        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.22/0.52        | ~ (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_A))
% 0.22/0.52        | (r2_hidden @ (k4_tarski @ sk_B_1 @ sk_D_1) @ (u1_orders_2 @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['17', '38'])).
% 0.22/0.52  thf('40', plain, ((l1_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('41', plain, ((v4_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('42', plain,
% 0.22/0.52      ((~ (r2_hidden @ sk_C_1 @ (u1_struct_0 @ sk_A))
% 0.22/0.52        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.22/0.52        | ~ (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_A))
% 0.22/0.52        | (r2_hidden @ (k4_tarski @ sk_B_1 @ sk_D_1) @ (u1_orders_2 @ sk_A)))),
% 0.22/0.52      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.22/0.52  thf('43', plain,
% 0.22/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.52        | (r2_hidden @ (k4_tarski @ sk_B_1 @ sk_D_1) @ (u1_orders_2 @ sk_A))
% 0.22/0.52        | ~ (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_A))
% 0.22/0.52        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['16', '42'])).
% 0.22/0.52  thf('44', plain,
% 0.22/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.52        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.22/0.52        | (r2_hidden @ (k4_tarski @ sk_B_1 @ sk_D_1) @ (u1_orders_2 @ sk_A))
% 0.22/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['13', '43'])).
% 0.22/0.52  thf('45', plain,
% 0.22/0.52      (((r2_hidden @ (k4_tarski @ sk_B_1 @ sk_D_1) @ (u1_orders_2 @ sk_A))
% 0.22/0.52        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.22/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('simplify', [status(thm)], ['44'])).
% 0.22/0.52  thf('46', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('47', plain,
% 0.22/0.52      (![X3 : $i, X4 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X3 @ X4)
% 0.22/0.52          | (r2_hidden @ X3 @ X4)
% 0.22/0.52          | (v1_xboole_0 @ X4))),
% 0.22/0.52      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.22/0.52  thf('48', plain,
% 0.22/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.52        | (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['46', '47'])).
% 0.22/0.52  thf('49', plain,
% 0.22/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.52        | (r2_hidden @ (k4_tarski @ sk_B_1 @ sk_D_1) @ (u1_orders_2 @ sk_A)))),
% 0.22/0.52      inference('clc', [status(thm)], ['45', '48'])).
% 0.22/0.52  thf('50', plain,
% 0.22/0.52      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.22/0.52          | ~ (r2_hidden @ (k4_tarski @ X20 @ X22) @ (u1_orders_2 @ X21))
% 0.22/0.52          | (r1_orders_2 @ X21 @ X20 @ X22)
% 0.22/0.52          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.22/0.52          | ~ (l1_orders_2 @ X21))),
% 0.22/0.52      inference('cnf', [status(esa)], [d9_orders_2])).
% 0.22/0.52  thf('51', plain,
% 0.22/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.52        | ~ (l1_orders_2 @ sk_A)
% 0.22/0.52        | ~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))
% 0.22/0.52        | (r1_orders_2 @ sk_A @ sk_B_1 @ sk_D_1)
% 0.22/0.52        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['49', '50'])).
% 0.22/0.52  thf('52', plain, ((l1_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('53', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('54', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('55', plain,
% 0.22/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.52        | (r1_orders_2 @ sk_A @ sk_B_1 @ sk_D_1))),
% 0.22/0.52      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 0.22/0.52  thf('56', plain, (~ (r1_orders_2 @ sk_A @ sk_B_1 @ sk_D_1)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('57', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.22/0.52      inference('clc', [status(thm)], ['55', '56'])).
% 0.22/0.52  thf('58', plain,
% 0.22/0.52      (![X23 : $i]:
% 0.22/0.52         ((m1_subset_1 @ (u1_orders_2 @ X23) @ 
% 0.22/0.52           (k1_zfmisc_1 @ 
% 0.22/0.52            (k2_zfmisc_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X23))))
% 0.22/0.52          | ~ (l1_orders_2 @ X23))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.22/0.52  thf(cc4_relset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( v1_xboole_0 @ A ) =>
% 0.22/0.52       ( ![C:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.22/0.52           ( v1_xboole_0 @ C ) ) ) ))).
% 0.22/0.52  thf('59', plain,
% 0.22/0.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.52         (~ (v1_xboole_0 @ X10)
% 0.22/0.52          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X10)))
% 0.22/0.52          | (v1_xboole_0 @ X11))),
% 0.22/0.52      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.22/0.52  thf('60', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (l1_orders_2 @ X0)
% 0.22/0.52          | (v1_xboole_0 @ (u1_orders_2 @ X0))
% 0.22/0.52          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['58', '59'])).
% 0.22/0.52  thf('61', plain,
% 0.22/0.52      (((v1_xboole_0 @ (u1_orders_2 @ sk_A)) | ~ (l1_orders_2 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['57', '60'])).
% 0.22/0.52  thf('62', plain, ((l1_orders_2 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('63', plain, ((v1_xboole_0 @ (u1_orders_2 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['61', '62'])).
% 0.22/0.52  thf('64', plain, ($false), inference('demod', [status(thm)], ['10', '63'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
