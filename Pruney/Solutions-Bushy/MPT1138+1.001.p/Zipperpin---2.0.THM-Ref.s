%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1138+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wiLzUT2KnF

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:07 EST 2020

% Result     : Theorem 10.12s
% Output     : Refutation 10.12s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 670 expanded)
%              Number of leaves         :   31 ( 206 expanded)
%              Depth                    :   32
%              Number of atoms          : 2112 (10137 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r8_relat_2_type,type,(
    r8_relat_2: $i > $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
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

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( r1_orders_2 @ X11 @ X10 @ X12 )
      | ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( u1_orders_2 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('11',plain,(
    ! [X13: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X13 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('12',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( m1_subset_1 @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ X1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( m1_subset_1 @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r2_hidden @ X19 @ X20 )
      | ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t106_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('19',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X14 @ X15 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ ( k2_zfmisc_1 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X13: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X13 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('22',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ~ ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( u1_orders_2 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( u1_orders_2 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r2_hidden @ X19 @ X20 )
      | ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ ( k2_zfmisc_1 @ X15 @ X18 ) )
      | ~ ( r2_hidden @ X16 @ X18 )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B @ sk_D_1 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','26'])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('35',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ~ ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('36',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r2_hidden @ ( k4_tarski @ sk_B @ sk_D_1 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X16 @ X17 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ ( k2_zfmisc_1 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('39',plain,(
    r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( r1_orders_2 @ X11 @ X10 @ X12 )
      | ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( u1_orders_2 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_D_1 ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,(
    r1_orders_2 @ sk_A @ sk_C_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_D_1 ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X13: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X13 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

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

thf('53',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r8_relat_2 @ X5 @ X6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ X5 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X7 @ X6 )
      | ~ ( r2_hidden @ X9 @ X6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X5 )
      | ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_2])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ sk_B @ X1 )
      | ~ ( r2_hidden @ sk_C_1 @ X1 )
      | ~ ( r8_relat_2 @ ( u1_orders_2 @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(d5_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v4_orders_2 @ A )
      <=> ( r8_relat_2 @ ( u1_orders_2 @ A ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('57',plain,(
    ! [X3: $i] :
      ( ~ ( v4_orders_2 @ X3 )
      | ( r8_relat_2 @ ( u1_orders_2 @ X3 ) @ ( u1_struct_0 @ X3 ) )
      | ~ ( l1_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d5_orders_2])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('59',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X4 @ X5 ) @ ( sk_E @ X4 @ X5 ) ) @ X5 )
      | ( r8_relat_2 @ X5 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_2])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ X1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( m1_subset_1 @ ( k4_tarski @ ( sk_D @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( k4_tarski @ ( sk_D @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( m1_subset_1 @ ( k4_tarski @ ( sk_D @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r2_hidden @ X19 @ X20 )
      | ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X16 @ X17 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ ( k2_zfmisc_1 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r2_hidden @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('69',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X4 @ X5 ) @ ( sk_D @ X4 @ X5 ) ) @ X5 )
      | ( r8_relat_2 @ X5 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_2])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ X1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( m1_subset_1 @ ( k4_tarski @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_D @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( k4_tarski @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_D @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( m1_subset_1 @ ( k4_tarski @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_D @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r2_hidden @ X19 @ X20 )
      | ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_D @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X14 @ X15 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ ( k2_zfmisc_1 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('79',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X14 @ X15 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ ( k2_zfmisc_1 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r2_hidden @ ( sk_D @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X4 @ X5 ) @ ( sk_E @ X4 @ X5 ) ) @ X5 )
      | ( r8_relat_2 @ X5 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_2])).

thf('82',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X4 @ X5 ) @ ( sk_D @ X4 @ X5 ) ) @ X5 )
      | ( r8_relat_2 @ X5 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_2])).

thf('83',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r8_relat_2 @ X5 @ X6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ X5 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X7 @ X6 )
      | ~ ( r2_hidden @ X9 @ X6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X5 )
      | ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_2])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r8_relat_2 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ X2 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ X1 @ X0 ) @ X2 ) @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ X0 ) @ X3 )
      | ~ ( r8_relat_2 @ X0 @ X3 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r8_relat_2 @ X0 @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ X0 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X3 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ X1 @ X0 ) @ X2 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ X2 ) @ X0 )
      | ( r8_relat_2 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r8_relat_2 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r8_relat_2 @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_E @ X1 @ X0 ) ) @ X0 )
      | ~ ( r2_hidden @ ( sk_E @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ X0 ) @ X2 )
      | ~ ( r8_relat_2 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['81','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r8_relat_2 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_E @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_E @ X1 @ X0 ) ) @ X0 )
      | ( r8_relat_2 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( u1_orders_2 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['80','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( u1_orders_2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( u1_orders_2 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['77','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( u1_orders_2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( u1_orders_2 @ X0 ) )
      | ~ ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( u1_orders_2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['57','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( u1_orders_2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( u1_orders_2 @ X0 ) ) @ ( sk_E @ X1 @ ( u1_orders_2 @ X0 ) ) ) @ ( u1_orders_2 @ X0 ) )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X4 @ X5 ) @ ( sk_E @ X4 @ X5 ) ) @ X5 )
      | ( r8_relat_2 @ X5 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_2])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['55','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ( r8_relat_2 @ ( u1_orders_2 @ X0 ) @ X1 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','26'])).

thf('104',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r2_hidden @ X19 @ X20 )
      | ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('106',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ ( k2_zfmisc_1 @ X15 @ X18 ) )
      | ~ ( r2_hidden @ X16 @ X18 )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ sk_B ) @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B @ sk_B ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['103','108'])).

thf('110',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('111',plain,(
    r2_hidden @ ( k4_tarski @ sk_B @ sk_B ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ~ ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('113',plain,(
    ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ( r8_relat_2 @ ( u1_orders_2 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','113'])).

thf('115',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X0: $i] :
      ( r8_relat_2 @ ( u1_orders_2 @ sk_A ) @ X0 ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ sk_B @ X1 )
      | ~ ( r2_hidden @ sk_C_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['54','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( r2_hidden @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X1 ) @ ( u1_orders_2 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ X1 ) @ ( u1_orders_2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','118'])).

thf('120',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X1 ) @ ( u1_orders_2 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ X1 ) @ ( u1_orders_2 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ sk_B @ sk_D_1 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r2_hidden @ sk_D_1 @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ~ ( r2_hidden @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','121'])).

thf('123',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_D_1 ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','122'])).

thf('124',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('125',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X16 @ X17 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ ( k2_zfmisc_1 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('126',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ sk_B ) @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('129',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_B ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B @ sk_B ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ~ ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('132',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ( r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['126','132'])).

thf('134',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('135',plain,(
    r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['133','134'])).

thf('136',plain,(
    r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','26'])).

thf('137',plain,(
    r2_hidden @ ( k4_tarski @ sk_B @ sk_D_1 ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['123','135','136'])).

thf('138',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( u1_orders_2 @ X11 ) )
      | ( r1_orders_2 @ X11 @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('139',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_D_1 )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_D_1 ),
    inference(demod,[status(thm)],['139','140','141','142'])).

thf('144',plain,(
    $false ),
    inference(demod,[status(thm)],['0','143'])).


%------------------------------------------------------------------------------
