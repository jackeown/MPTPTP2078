%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0916+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LvO0pAZ2RD

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:42 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  264 ( 641 expanded)
%              Number of leaves         :   32 ( 217 expanded)
%              Depth                    :   56
%              Number of atoms          : 3002 (7977 expanded)
%              Number of equality atoms :  463 ( 696 expanded)
%              Maximal formula depth    :   26 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(t76_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
     => ! [E: $i] :
          ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) )
         => ! [F: $i] :
              ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) )
             => ! [G: $i] :
                  ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) )
                 => ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) )
                   => ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D )
                      & ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E )
                      & ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
       => ! [E: $i] :
            ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) )
           => ! [F: $i] :
                ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) )
               => ! [G: $i] :
                    ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) )
                   => ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) )
                     => ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D )
                        & ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E )
                        & ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_mcart_1])).

thf('0',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('1',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X33 @ X34 )
      | ~ ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('2',plain,(
    ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t35_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) )
    <=> ( ( k3_zfmisc_1 @ A @ B @ C )
       != k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ( X20 != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X17 @ X18 @ X20 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('4',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_zfmisc_1 @ X17 @ X18 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('5',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('6',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('7',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_zfmisc_1 @ X17 @ X18 @ o_0_0_xboole_0 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('8',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ ( sk_B @ X12 ) @ X12 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(dt_k5_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( m1_subset_1 @ ( k5_mcart_1 @ X0 @ X1 @ X2 @ X3 ) @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( k3_zfmisc_1 @ X0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_mcart_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k5_mcart_1 @ X2 @ X1 @ X0 @ ( sk_B @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) ) ) @ X2 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k5_mcart_1 @ X0 @ X1 @ o_0_0_xboole_0 @ ( sk_B @ o_0_0_xboole_0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k5_mcart_1 @ X0 @ X1 @ o_0_0_xboole_0 @ ( sk_B @ o_0_0_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k5_mcart_1 @ X0 @ X1 @ o_0_0_xboole_0 @ ( sk_B @ o_0_0_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k5_mcart_1 @ X0 @ X1 @ o_0_0_xboole_0 @ ( sk_B @ o_0_0_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('16',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ X13 @ X14 )
      | ~ ( r2_hidden @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('18',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( m1_subset_1 @ ( k5_mcart_1 @ X0 @ X1 @ X2 @ X3 ) @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( k3_zfmisc_1 @ X0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_mcart_1])).

thf('20',plain,(
    m1_subset_1 @ ( k5_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_G ) @ sk_D ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('22',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( r2_hidden @ ( k5_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('24',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t75_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 )
        & ( E != k1_xboole_0 )
        & ( F != k1_xboole_0 )
        & ? [G: $i] :
            ( ? [H: $i] :
                ( ~ ( ( ( k5_mcart_1 @ A @ B @ C @ G )
                      = ( k5_mcart_1 @ D @ E @ F @ H ) )
                    & ( ( k6_mcart_1 @ A @ B @ C @ G )
                      = ( k6_mcart_1 @ D @ E @ F @ H ) )
                    & ( ( k7_mcart_1 @ A @ B @ C @ G )
                      = ( k7_mcart_1 @ D @ E @ F @ H ) ) )
                & ( G = H )
                & ( m1_subset_1 @ H @ ( k3_zfmisc_1 @ D @ E @ F ) ) )
            & ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) ) ) )).

thf('25',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ( X28 = k1_xboole_0 )
      | ( X29 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X30 @ ( k3_zfmisc_1 @ X28 @ X29 @ X31 ) )
      | ( X32 != X30 )
      | ( ( k5_mcart_1 @ X25 @ X26 @ X27 @ X32 )
        = ( k5_mcart_1 @ X28 @ X29 @ X31 @ X30 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k3_zfmisc_1 @ X25 @ X26 @ X27 ) )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t75_mcart_1])).

thf('26',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( X31 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X30 @ ( k3_zfmisc_1 @ X25 @ X26 @ X27 ) )
      | ( ( k5_mcart_1 @ X25 @ X26 @ X27 @ X30 )
        = ( k5_mcart_1 @ X28 @ X29 @ X31 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k3_zfmisc_1 @ X28 @ X29 @ X31 ) )
      | ( X29 = k1_xboole_0 )
      | ( X28 = k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('28',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('29',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('30',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('31',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('32',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('33',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( X31 = o_0_0_xboole_0 )
      | ~ ( m1_subset_1 @ X30 @ ( k3_zfmisc_1 @ X25 @ X26 @ X27 ) )
      | ( ( k5_mcart_1 @ X25 @ X26 @ X27 @ X30 )
        = ( k5_mcart_1 @ X28 @ X29 @ X31 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k3_zfmisc_1 @ X28 @ X29 @ X31 ) )
      | ( X29 = o_0_0_xboole_0 )
      | ( X28 = o_0_0_xboole_0 )
      | ( X27 = o_0_0_xboole_0 )
      | ( X26 = o_0_0_xboole_0 )
      | ( X25 = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','27','28','29','30','31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( sk_A = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( X0 = o_0_0_xboole_0 )
      | ( X1 = o_0_0_xboole_0 )
      | ~ ( m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ X0 @ X1 @ X2 ) )
      | ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G )
        = ( k5_mcart_1 @ X0 @ X1 @ X2 @ sk_G ) )
      | ( X2 = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','33'])).

thf('35',plain,
    ( ( sk_F = o_0_0_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G )
      = ( k5_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_G ) )
    | ( sk_E = o_0_0_xboole_0 )
    | ( sk_D = o_0_0_xboole_0 )
    | ( sk_C = o_0_0_xboole_0 )
    | ( sk_B_1 = o_0_0_xboole_0 )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','34'])).

thf('36',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D )
    | ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( r2_hidden @ ( k5_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('39',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(dt_k6_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k6_mcart_1 @ A @ B @ C @ D ) @ B ) ) )).

thf('40',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k6_mcart_1 @ X4 @ X5 @ X6 @ X7 ) @ X5 )
      | ~ ( m1_subset_1 @ X7 @ ( k3_zfmisc_1 @ X4 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_mcart_1])).

thf('41',plain,(
    m1_subset_1 @ ( k6_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_G ) @ sk_E ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('43',plain,
    ( ( v1_xboole_0 @ sk_E )
    | ( r2_hidden @ ( k6_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(dt_k7_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ) )).

thf('45',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( m1_subset_1 @ ( k7_mcart_1 @ X8 @ X9 @ X10 @ X11 ) @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k3_zfmisc_1 @ X8 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_mcart_1])).

thf('46',plain,(
    m1_subset_1 @ ( k7_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('48',plain,
    ( ( v1_xboole_0 @ sk_F )
    | ( r2_hidden @ ( k7_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( v1_xboole_0 @ sk_F )
    | ( r2_hidden @ ( k7_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('50',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('51',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ( X28 = k1_xboole_0 )
      | ( X29 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X30 @ ( k3_zfmisc_1 @ X28 @ X29 @ X31 ) )
      | ( X32 != X30 )
      | ( ( k7_mcart_1 @ X25 @ X26 @ X27 @ X32 )
        = ( k7_mcart_1 @ X28 @ X29 @ X31 @ X30 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k3_zfmisc_1 @ X25 @ X26 @ X27 ) )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t75_mcart_1])).

thf('53',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( X31 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X30 @ ( k3_zfmisc_1 @ X25 @ X26 @ X27 ) )
      | ( ( k7_mcart_1 @ X25 @ X26 @ X27 @ X30 )
        = ( k7_mcart_1 @ X28 @ X29 @ X31 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k3_zfmisc_1 @ X28 @ X29 @ X31 ) )
      | ( X29 = k1_xboole_0 )
      | ( X28 = k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('55',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('56',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('57',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('58',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('59',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('60',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( X31 = o_0_0_xboole_0 )
      | ~ ( m1_subset_1 @ X30 @ ( k3_zfmisc_1 @ X25 @ X26 @ X27 ) )
      | ( ( k7_mcart_1 @ X25 @ X26 @ X27 @ X30 )
        = ( k7_mcart_1 @ X28 @ X29 @ X31 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k3_zfmisc_1 @ X28 @ X29 @ X31 ) )
      | ( X29 = o_0_0_xboole_0 )
      | ( X28 = o_0_0_xboole_0 )
      | ( X27 = o_0_0_xboole_0 )
      | ( X26 = o_0_0_xboole_0 )
      | ( X25 = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['53','54','55','56','57','58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( sk_A = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( X0 = o_0_0_xboole_0 )
      | ( X1 = o_0_0_xboole_0 )
      | ~ ( m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ X0 @ X1 @ X2 ) )
      | ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G )
        = ( k7_mcart_1 @ X0 @ X1 @ X2 @ sk_G ) )
      | ( X2 = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','60'])).

thf('62',plain,
    ( ( sk_F = o_0_0_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G )
      = ( k7_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_G ) )
    | ( sk_E = o_0_0_xboole_0 )
    | ( sk_D = o_0_0_xboole_0 )
    | ( sk_C = o_0_0_xboole_0 )
    | ( sk_B_1 = o_0_0_xboole_0 )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','61'])).

thf('63',plain,
    ( ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['36'])).

thf('64',plain,
    ( ( ~ ( r2_hidden @ ( k7_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_G ) @ sk_F )
      | ( sk_A = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( v1_xboole_0 @ sk_F )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['49','64'])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('66',plain,(
    ! [X24: $i] :
      ( ( X24 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('67',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('68',plain,(
    ! [X24: $i] :
      ( ( X24 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X24 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( sk_A = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,
    ( ( ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('72',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X21 @ X22 )
      | ~ ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
        | ( sk_A = o_0_0_xboole_0 )
        | ( sk_B_1 = o_0_0_xboole_0 )
        | ( sk_D = o_0_0_xboole_0 )
        | ( sk_E = o_0_0_xboole_0 )
        | ( sk_F = o_0_0_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('75',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('76',plain,
    ( ! [X0: $i] :
        ( ( sk_A = o_0_0_xboole_0 )
        | ( sk_B_1 = o_0_0_xboole_0 )
        | ( sk_D = o_0_0_xboole_0 )
        | ( sk_E = o_0_0_xboole_0 )
        | ( sk_F = o_0_0_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( v1_xboole_0 @ sk_F )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['48','76'])).

thf('78',plain,(
    ! [X24: $i] :
      ( ( X24 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X24 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('79',plain,
    ( ( ( sk_A = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X21 @ X22 )
      | ~ ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
        | ( sk_A = o_0_0_xboole_0 )
        | ( sk_D = o_0_0_xboole_0 )
        | ( sk_E = o_0_0_xboole_0 )
        | ( sk_F = o_0_0_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('86',plain,
    ( ! [X0: $i] :
        ( ( sk_A = o_0_0_xboole_0 )
        | ( sk_D = o_0_0_xboole_0 )
        | ( sk_E = o_0_0_xboole_0 )
        | ( sk_F = o_0_0_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( v1_xboole_0 @ sk_E )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['43','86'])).

thf('88',plain,(
    ! [X24: $i] :
      ( ( X24 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X24 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('89',plain,
    ( ( ( sk_A = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X21 @ X22 )
      | ~ ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
        | ( sk_D = o_0_0_xboole_0 )
        | ( sk_E = o_0_0_xboole_0 )
        | ( sk_F = o_0_0_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_D ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf('95',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('96',plain,
    ( ! [X0: $i] :
        ( ( sk_D = o_0_0_xboole_0 )
        | ( sk_E = o_0_0_xboole_0 )
        | ( sk_F = o_0_0_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_D ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ( v1_xboole_0 @ sk_D )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['38','96'])).

thf('98',plain,(
    ! [X24: $i] :
      ( ( X24 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X24 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('99',plain,
    ( ( ( sk_D = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('102',plain,
    ( ( ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_D @ sk_E @ o_0_0_xboole_0 ) )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_zfmisc_1 @ X17 @ X18 @ o_0_0_xboole_0 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('104',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('105',plain,
    ( ( ( sk_D = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,(
    ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('107',plain,
    ( ( ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_D @ o_0_0_xboole_0 @ sk_F ) )
      | ( sk_D = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ( X18 != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X17 @ X18 @ X20 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('109',plain,(
    ! [X17: $i,X20: $i] :
      ( ( k3_zfmisc_1 @ X17 @ k1_xboole_0 @ X20 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('111',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('112',plain,(
    ! [X17: $i,X20: $i] :
      ( ( k3_zfmisc_1 @ X17 @ o_0_0_xboole_0 @ X20 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('114',plain,
    ( ( sk_D = o_0_0_xboole_0 )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['107','112','113'])).

thf('115',plain,(
    ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('116',plain,
    ( ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ o_0_0_xboole_0 @ sk_E @ sk_F ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ( X17 != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X17 @ X18 @ X20 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('118',plain,(
    ! [X18: $i,X20: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X18 @ X20 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('120',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('121',plain,(
    ! [X18: $i,X20: $i] :
      ( ( k3_zfmisc_1 @ o_0_0_xboole_0 @ X18 @ X20 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['118','119','120'])).

thf('122',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('123',plain,(
    r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ),
    inference(demod,[status(thm)],['116','121','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k5_mcart_1 @ X0 @ X1 @ o_0_0_xboole_0 @ ( sk_B @ o_0_0_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k5_mcart_1 @ X0 @ X1 @ o_0_0_xboole_0 @ ( sk_B @ o_0_0_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k5_mcart_1 @ X0 @ X1 @ o_0_0_xboole_0 @ ( sk_B @ o_0_0_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('127',plain,
    ( ( v1_xboole_0 @ sk_E )
    | ( r2_hidden @ ( k6_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('128',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('129',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ( X28 = k1_xboole_0 )
      | ( X29 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X30 @ ( k3_zfmisc_1 @ X28 @ X29 @ X31 ) )
      | ( X32 != X30 )
      | ( ( k6_mcart_1 @ X25 @ X26 @ X27 @ X32 )
        = ( k6_mcart_1 @ X28 @ X29 @ X31 @ X30 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k3_zfmisc_1 @ X25 @ X26 @ X27 ) )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t75_mcart_1])).

thf('131',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( X31 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X30 @ ( k3_zfmisc_1 @ X25 @ X26 @ X27 ) )
      | ( ( k6_mcart_1 @ X25 @ X26 @ X27 @ X30 )
        = ( k6_mcart_1 @ X28 @ X29 @ X31 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k3_zfmisc_1 @ X28 @ X29 @ X31 ) )
      | ( X29 = k1_xboole_0 )
      | ( X28 = k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('133',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('134',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('135',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('136',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('137',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('138',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( X31 = o_0_0_xboole_0 )
      | ~ ( m1_subset_1 @ X30 @ ( k3_zfmisc_1 @ X25 @ X26 @ X27 ) )
      | ( ( k6_mcart_1 @ X25 @ X26 @ X27 @ X30 )
        = ( k6_mcart_1 @ X28 @ X29 @ X31 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k3_zfmisc_1 @ X28 @ X29 @ X31 ) )
      | ( X29 = o_0_0_xboole_0 )
      | ( X28 = o_0_0_xboole_0 )
      | ( X27 = o_0_0_xboole_0 )
      | ( X26 = o_0_0_xboole_0 )
      | ( X25 = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['131','132','133','134','135','136','137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( sk_A = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( X0 = o_0_0_xboole_0 )
      | ( X1 = o_0_0_xboole_0 )
      | ~ ( m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ X0 @ X1 @ X2 ) )
      | ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G )
        = ( k6_mcart_1 @ X0 @ X1 @ X2 @ sk_G ) )
      | ( X2 = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['129','138'])).

thf('140',plain,
    ( ( sk_F = o_0_0_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G )
      = ( k6_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_G ) )
    | ( sk_E = o_0_0_xboole_0 )
    | ( sk_D = o_0_0_xboole_0 )
    | ( sk_C = o_0_0_xboole_0 )
    | ( sk_B_1 = o_0_0_xboole_0 )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['128','139'])).

thf('141',plain,
    ( ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference(split,[status(esa)],['36'])).

thf('142',plain,
    ( ( ~ ( r2_hidden @ ( k6_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_G ) @ sk_E )
      | ( sk_A = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ( ( v1_xboole_0 @ sk_E )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['127','142'])).

thf('144',plain,(
    ! [X24: $i] :
      ( ( X24 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X24 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('145',plain,
    ( ( ( sk_A = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,
    ( ( ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('148',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
        | ( sk_A = o_0_0_xboole_0 )
        | ( sk_B_1 = o_0_0_xboole_0 )
        | ( sk_D = o_0_0_xboole_0 )
        | ( sk_E = o_0_0_xboole_0 )
        | ( sk_F = o_0_0_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('150',plain,
    ( ! [X0: $i] :
        ( ( sk_A = o_0_0_xboole_0 )
        | ( sk_B_1 = o_0_0_xboole_0 )
        | ( sk_D = o_0_0_xboole_0 )
        | ( sk_E = o_0_0_xboole_0 )
        | ( sk_F = o_0_0_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,
    ( ( ( v1_xboole_0 @ sk_F )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['126','150'])).

thf('152',plain,(
    ! [X24: $i] :
      ( ( X24 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X24 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('153',plain,
    ( ( ( sk_A = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,
    ( ( ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('156',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
        | ( sk_A = o_0_0_xboole_0 )
        | ( sk_D = o_0_0_xboole_0 )
        | ( sk_E = o_0_0_xboole_0 )
        | ( sk_F = o_0_0_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('158',plain,
    ( ! [X0: $i] :
        ( ( sk_A = o_0_0_xboole_0 )
        | ( sk_D = o_0_0_xboole_0 )
        | ( sk_E = o_0_0_xboole_0 )
        | ( sk_F = o_0_0_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,
    ( ( ( v1_xboole_0 @ sk_E )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['125','158'])).

thf('160',plain,(
    ! [X24: $i] :
      ( ( X24 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X24 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('161',plain,
    ( ( ( sk_A = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,
    ( ( ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('164',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
        | ( sk_D = o_0_0_xboole_0 )
        | ( sk_E = o_0_0_xboole_0 )
        | ( sk_F = o_0_0_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_D ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('166',plain,
    ( ! [X0: $i] :
        ( ( sk_D = o_0_0_xboole_0 )
        | ( sk_E = o_0_0_xboole_0 )
        | ( sk_F = o_0_0_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_D ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,
    ( ( ( v1_xboole_0 @ sk_D )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['124','166'])).

thf('168',plain,(
    ! [X24: $i] :
      ( ( X24 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X24 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('169',plain,
    ( ( ( sk_D = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,
    ( ( ( sk_F = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference(simplify,[status(thm)],['169'])).

thf('171',plain,(
    ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('172',plain,
    ( ( ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_D @ sk_E @ o_0_0_xboole_0 ) )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_zfmisc_1 @ X17 @ X18 @ o_0_0_xboole_0 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('174',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('175',plain,
    ( ( ( sk_D = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference(demod,[status(thm)],['172','173','174'])).

thf('176',plain,(
    ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('177',plain,
    ( ( ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_D @ o_0_0_xboole_0 @ sk_F ) )
      | ( sk_D = o_0_0_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    ! [X17: $i,X20: $i] :
      ( ( k3_zfmisc_1 @ X17 @ o_0_0_xboole_0 @ X20 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('179',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('180',plain,
    ( ( sk_D = o_0_0_xboole_0 )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference(demod,[status(thm)],['177','178','179'])).

thf('181',plain,(
    ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('182',plain,
    ( ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ o_0_0_xboole_0 @ sk_E @ sk_F ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X18: $i,X20: $i] :
      ( ( k3_zfmisc_1 @ o_0_0_xboole_0 @ X18 @ X20 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['118','119','120'])).

thf('184',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('185',plain,(
    r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ),
    inference(demod,[status(thm)],['182','183','184'])).

thf('186',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D )
    | ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['36'])).

thf('187',plain,(
    ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['123','185','186'])).

thf('188',plain,(
    ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['37','187'])).

thf('189',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_D @ sk_E @ sk_F @ sk_G ) @ sk_D )
    | ( sk_A = o_0_0_xboole_0 )
    | ( sk_B_1 = o_0_0_xboole_0 )
    | ( sk_C = o_0_0_xboole_0 )
    | ( sk_D = o_0_0_xboole_0 )
    | ( sk_E = o_0_0_xboole_0 )
    | ( sk_F = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','188'])).

thf('190',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( sk_F = o_0_0_xboole_0 )
    | ( sk_E = o_0_0_xboole_0 )
    | ( sk_D = o_0_0_xboole_0 )
    | ( sk_C = o_0_0_xboole_0 )
    | ( sk_B_1 = o_0_0_xboole_0 )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','189'])).

thf('191',plain,(
    ! [X24: $i] :
      ( ( X24 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X24 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('192',plain,
    ( ( sk_A = o_0_0_xboole_0 )
    | ( sk_B_1 = o_0_0_xboole_0 )
    | ( sk_C = o_0_0_xboole_0 )
    | ( sk_D = o_0_0_xboole_0 )
    | ( sk_E = o_0_0_xboole_0 )
    | ( sk_F = o_0_0_xboole_0 )
    | ( sk_D = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,
    ( ( sk_F = o_0_0_xboole_0 )
    | ( sk_E = o_0_0_xboole_0 )
    | ( sk_D = o_0_0_xboole_0 )
    | ( sk_C = o_0_0_xboole_0 )
    | ( sk_B_1 = o_0_0_xboole_0 )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference(simplify,[status(thm)],['192'])).

thf('194',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('195',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('197',plain,(
    ! [X0: $i] :
      ( ( sk_A = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference(demod,[status(thm)],['195','196'])).

thf('198',plain,
    ( ( v1_xboole_0 @ sk_F )
    | ( sk_F = o_0_0_xboole_0 )
    | ( sk_E = o_0_0_xboole_0 )
    | ( sk_D = o_0_0_xboole_0 )
    | ( sk_B_1 = o_0_0_xboole_0 )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','197'])).

thf('199',plain,(
    ! [X24: $i] :
      ( ( X24 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X24 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('200',plain,
    ( ( sk_A = o_0_0_xboole_0 )
    | ( sk_B_1 = o_0_0_xboole_0 )
    | ( sk_D = o_0_0_xboole_0 )
    | ( sk_E = o_0_0_xboole_0 )
    | ( sk_F = o_0_0_xboole_0 )
    | ( sk_F = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,
    ( ( sk_F = o_0_0_xboole_0 )
    | ( sk_E = o_0_0_xboole_0 )
    | ( sk_D = o_0_0_xboole_0 )
    | ( sk_B_1 = o_0_0_xboole_0 )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference(simplify,[status(thm)],['200'])).

thf('202',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('203',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('205',plain,(
    ! [X0: $i] :
      ( ( sk_A = o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference(demod,[status(thm)],['203','204'])).

thf('206',plain,
    ( ( v1_xboole_0 @ sk_E )
    | ( sk_F = o_0_0_xboole_0 )
    | ( sk_E = o_0_0_xboole_0 )
    | ( sk_D = o_0_0_xboole_0 )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','205'])).

thf('207',plain,(
    ! [X24: $i] :
      ( ( X24 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X24 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('208',plain,
    ( ( sk_A = o_0_0_xboole_0 )
    | ( sk_D = o_0_0_xboole_0 )
    | ( sk_E = o_0_0_xboole_0 )
    | ( sk_F = o_0_0_xboole_0 )
    | ( sk_E = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,
    ( ( sk_F = o_0_0_xboole_0 )
    | ( sk_E = o_0_0_xboole_0 )
    | ( sk_D = o_0_0_xboole_0 )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference(simplify,[status(thm)],['208'])).

thf('210',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('211',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
      | ( sk_D = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['209','210'])).

thf('212',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('213',plain,(
    ! [X0: $i] :
      ( ( sk_D = o_0_0_xboole_0 )
      | ( sk_E = o_0_0_xboole_0 )
      | ( sk_F = o_0_0_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['211','212'])).

thf('214',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( sk_F = o_0_0_xboole_0 )
    | ( sk_E = o_0_0_xboole_0 )
    | ( sk_D = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','213'])).

thf('215',plain,(
    ! [X24: $i] :
      ( ( X24 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X24 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('216',plain,
    ( ( sk_D = o_0_0_xboole_0 )
    | ( sk_E = o_0_0_xboole_0 )
    | ( sk_F = o_0_0_xboole_0 )
    | ( sk_D = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('217',plain,
    ( ( sk_F = o_0_0_xboole_0 )
    | ( sk_E = o_0_0_xboole_0 )
    | ( sk_D = o_0_0_xboole_0 ) ),
    inference(simplify,[status(thm)],['216'])).

thf('218',plain,(
    ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('219',plain,
    ( ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_D @ sk_E @ o_0_0_xboole_0 ) )
    | ( sk_D = o_0_0_xboole_0 )
    | ( sk_E = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_zfmisc_1 @ X17 @ X18 @ o_0_0_xboole_0 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('221',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('222',plain,
    ( ( sk_D = o_0_0_xboole_0 )
    | ( sk_E = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['219','220','221'])).

thf('223',plain,(
    ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('224',plain,
    ( ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_D @ o_0_0_xboole_0 @ sk_F ) )
    | ( sk_D = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['222','223'])).

thf('225',plain,(
    ! [X17: $i,X20: $i] :
      ( ( k3_zfmisc_1 @ X17 @ o_0_0_xboole_0 @ X20 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('226',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('227',plain,(
    sk_D = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['224','225','226'])).

thf('228',plain,(
    ! [X18: $i,X20: $i] :
      ( ( k3_zfmisc_1 @ o_0_0_xboole_0 @ X18 @ X20 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['118','119','120'])).

thf('229',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('230',plain,(
    $false ),
    inference(demod,[status(thm)],['2','227','228','229'])).


%------------------------------------------------------------------------------
