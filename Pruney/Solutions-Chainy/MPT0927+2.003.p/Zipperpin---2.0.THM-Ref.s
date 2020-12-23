%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vIAew4fagt

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:19 EST 2020

% Result     : Theorem 1.04s
% Output     : Refutation 1.04s
% Verified   : 
% Statistics : Number of formulae       :  351 (1116 expanded)
%              Number of leaves         :   43 ( 352 expanded)
%              Depth                    :   53
%              Number of atoms          : 4011 (16341 expanded)
%              Number of equality atoms :  600 (1180 expanded)
%              Maximal formula depth    :   27 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k11_mcart_1_type,type,(
    k11_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k8_mcart_1_type,type,(
    k8_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k9_mcart_1_type,type,(
    k9_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k10_mcart_1_type,type,(
    k10_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_I_type,type,(
    sk_I: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(t87_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ A ) )
     => ! [F: $i] :
          ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ B ) )
         => ! [G: $i] :
              ( ( m1_subset_1 @ G @ ( k1_zfmisc_1 @ C ) )
             => ! [H: $i] :
                  ( ( m1_subset_1 @ H @ ( k1_zfmisc_1 @ D ) )
                 => ! [I: $i] :
                      ( ( m1_subset_1 @ I @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
                     => ( ( r2_hidden @ I @ ( k4_zfmisc_1 @ E @ F @ G @ H ) )
                       => ( ( r2_hidden @ ( k8_mcart_1 @ A @ B @ C @ D @ I ) @ E )
                          & ( r2_hidden @ ( k9_mcart_1 @ A @ B @ C @ D @ I ) @ F )
                          & ( r2_hidden @ ( k10_mcart_1 @ A @ B @ C @ D @ I ) @ G )
                          & ( r2_hidden @ ( k11_mcart_1 @ A @ B @ C @ D @ I ) @ H ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ A ) )
       => ! [F: $i] :
            ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ B ) )
           => ! [G: $i] :
                ( ( m1_subset_1 @ G @ ( k1_zfmisc_1 @ C ) )
               => ! [H: $i] :
                    ( ( m1_subset_1 @ H @ ( k1_zfmisc_1 @ D ) )
                   => ! [I: $i] :
                        ( ( m1_subset_1 @ I @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
                       => ( ( r2_hidden @ I @ ( k4_zfmisc_1 @ E @ F @ G @ H ) )
                         => ( ( r2_hidden @ ( k8_mcart_1 @ A @ B @ C @ D @ I ) @ E )
                            & ( r2_hidden @ ( k9_mcart_1 @ A @ B @ C @ D @ I ) @ F )
                            & ( r2_hidden @ ( k10_mcart_1 @ A @ B @ C @ D @ I ) @ G )
                            & ( r2_hidden @ ( k11_mcart_1 @ A @ B @ C @ D @ I ) @ H ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t87_mcart_1])).

thf('0',plain,(
    r2_hidden @ sk_I @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('2',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r2_hidden @ sk_I @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ( m1_subset_1 @ X16 @ X17 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('6',plain,(
    ! [X16: $i,X17: $i] :
      ( ( m1_subset_1 @ X16 @ X17 )
      | ~ ( r2_hidden @ X16 @ X17 ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf(t61_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 )
        & ~ ! [E: $i] :
              ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
             => ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E )
                  = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) )
                & ( ( k9_mcart_1 @ A @ B @ C @ D @ E )
                  = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) )
                & ( ( k10_mcart_1 @ A @ B @ C @ D @ E )
                  = ( k2_mcart_1 @ ( k1_mcart_1 @ E ) ) )
                & ( ( k11_mcart_1 @ A @ B @ C @ D @ E )
                  = ( k2_mcart_1 @ E ) ) ) ) ) )).

thf('8',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( X47 = k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( X49 = k1_xboole_0 )
      | ( ( k8_mcart_1 @ X47 @ X48 @ X49 @ X51 @ X50 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ X50 ) ) ) )
      | ~ ( m1_subset_1 @ X50 @ ( k4_zfmisc_1 @ X47 @ X48 @ X49 @ X51 ) )
      | ( X51 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('9',plain,
    ( ( sk_H = k1_xboole_0 )
    | ( ( k8_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) )
    | ( sk_G = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf(dt_k8_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ( m1_subset_1 @ ( k8_mcart_1 @ A @ B @ C @ D @ E ) @ A ) ) )).

thf('11',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( m1_subset_1 @ ( k8_mcart_1 @ X32 @ X33 @ X34 @ X35 @ X36 ) @ X32 )
      | ~ ( m1_subset_1 @ X36 @ ( k4_zfmisc_1 @ X32 @ X33 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_mcart_1])).

thf('12',plain,(
    m1_subset_1 @ ( k8_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) @ sk_E ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ X17 )
      | ( r2_hidden @ X16 @ X17 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('14',plain,
    ( ( v1_xboole_0 @ sk_E )
    | ( r2_hidden @ ( k8_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) @ sk_E ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('15',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('16',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf(t55_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 ) )
    <=> ( ( k4_zfmisc_1 @ A @ B @ C @ D )
       != k1_xboole_0 ) ) )).

thf('17',plain,(
    ! [X42: $i,X43: $i,X44: $i,X46: $i] :
      ( ( X42 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X42 @ X43 @ X44 @ X46 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('18',plain,(
    ! [X43: $i,X44: $i,X46: $i] :
      ( ( k4_zfmisc_1 @ k1_xboole_0 @ X43 @ X44 @ X46 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X0 @ X3 @ X2 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','18'])).

thf('20',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('21',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_E )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ~ ( v1_xboole_0 @ sk_E ) ),
    inference(condensation,[status(thm)],['23'])).

thf('25',plain,(
    r2_hidden @ ( k8_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) @ sk_E ),
    inference(clc,[status(thm)],['14','24'])).

thf('26',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_E )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( X47 = k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( X49 = k1_xboole_0 )
      | ( ( k8_mcart_1 @ X47 @ X48 @ X49 @ X51 @ X50 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ X50 ) ) ) )
      | ~ ( m1_subset_1 @ X50 @ ( k4_zfmisc_1 @ X47 @ X48 @ X49 @ X51 ) )
      | ( X51 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('29',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_E )
    | ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F )
    | ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G )
    | ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_E )
   <= ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_E ) ),
    inference(split,[status(esa)],['30'])).

thf('32',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('33',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( X47 = k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( X49 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X47 @ X48 @ X49 @ X51 @ X50 )
        = ( k2_mcart_1 @ X50 ) )
      | ~ ( m1_subset_1 @ X50 @ ( k4_zfmisc_1 @ X47 @ X48 @ X49 @ X51 ) )
      | ( X51 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('34',plain,
    ( ( sk_H = k1_xboole_0 )
    | ( ( k11_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I )
      = ( k2_mcart_1 @ sk_I ) )
    | ( sk_G = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf(dt_k11_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ( m1_subset_1 @ ( k11_mcart_1 @ A @ B @ C @ D @ E ) @ D ) ) )).

thf('36',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( m1_subset_1 @ ( k11_mcart_1 @ X27 @ X28 @ X29 @ X30 @ X31 ) @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k4_zfmisc_1 @ X27 @ X28 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k11_mcart_1])).

thf('37',plain,(
    m1_subset_1 @ ( k11_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) @ sk_H ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ X17 )
      | ( r2_hidden @ X16 @ X17 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('39',plain,
    ( ( v1_xboole_0 @ sk_H )
    | ( r2_hidden @ ( k11_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('41',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('42',plain,(
    ! [X42: $i,X43: $i,X44: $i,X46: $i] :
      ( ( X46 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X42 @ X43 @ X44 @ X46 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('43',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( k4_zfmisc_1 @ X42 @ X43 @ X44 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','43'])).

thf('45',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('46',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_H ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_H ) ) ),
    inference('sup-',[status(thm)],['40','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_H )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ~ ( v1_xboole_0 @ sk_H ) ),
    inference(condensation,[status(thm)],['48'])).

thf('50',plain,(
    r2_hidden @ ( k11_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) @ sk_H ),
    inference(clc,[status(thm)],['39','49'])).

thf('51',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ sk_I ) @ sk_H )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['34','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( X47 = k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( X49 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X47 @ X48 @ X49 @ X51 @ X50 )
        = ( k2_mcart_1 @ X50 ) )
      | ~ ( m1_subset_1 @ X50 @ ( k4_zfmisc_1 @ X47 @ X48 @ X49 @ X51 ) )
      | ( X51 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('54',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I )
      = ( k2_mcart_1 @ sk_I ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(split,[status(esa)],['30'])).

thf('56',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_I ) @ sk_H )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( sk_H = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_H @ ( k1_zfmisc_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('59',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('60',plain,(
    r1_tarski @ sk_H @ sk_D ),
    inference('sup-',[status(thm)],['58','59'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('61',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('62',plain,
    ( ( k3_xboole_0 @ sk_H @ sk_D )
    = sk_H ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( ( k3_xboole_0 @ sk_H @ k1_xboole_0 )
        = sk_H )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup+',[status(thm)],['57','62'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('64',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('65',plain,
    ( ( ( k1_xboole_0 = sk_H )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( sk_G = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( k1_xboole_0 = sk_H ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('69',plain,(
    r1_tarski @ sk_G @ sk_C ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('71',plain,
    ( ( k3_xboole_0 @ sk_G @ sk_C )
    = sk_G ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( ( k3_xboole_0 @ sk_G @ k1_xboole_0 )
        = sk_G )
      | ( k1_xboole_0 = sk_H )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup+',[status(thm)],['66','71'])).

thf('73',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('74',plain,
    ( ( ( k1_xboole_0 = sk_G )
      | ( k1_xboole_0 = sk_H )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( sk_F = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( k1_xboole_0 = sk_H )
      | ( k1_xboole_0 = sk_G ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('78',plain,(
    r1_tarski @ sk_F @ sk_B_1 ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('80',plain,
    ( ( k3_xboole_0 @ sk_F @ sk_B_1 )
    = sk_F ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( ( k3_xboole_0 @ sk_F @ k1_xboole_0 )
        = sk_F )
      | ( k1_xboole_0 = sk_G )
      | ( k1_xboole_0 = sk_H )
      | ( sk_A = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup+',[status(thm)],['75','80'])).

thf('82',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('83',plain,
    ( ( ( k1_xboole_0 = sk_F )
      | ( k1_xboole_0 = sk_G )
      | ( k1_xboole_0 = sk_H )
      | ( sk_A = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( sk_E = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( k1_xboole_0 = sk_H )
      | ( k1_xboole_0 = sk_G )
      | ( k1_xboole_0 = sk_F ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('87',plain,(
    r1_tarski @ sk_E @ sk_A ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('89',plain,
    ( ( k3_xboole_0 @ sk_E @ sk_A )
    = sk_E ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ( ( k3_xboole_0 @ sk_E @ k1_xboole_0 )
        = sk_E )
      | ( k1_xboole_0 = sk_F )
      | ( k1_xboole_0 = sk_G )
      | ( k1_xboole_0 = sk_H )
      | ( sk_E = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup+',[status(thm)],['84','89'])).

thf('91',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('92',plain,
    ( ( ( k1_xboole_0 = sk_E )
      | ( k1_xboole_0 = sk_F )
      | ( k1_xboole_0 = sk_G )
      | ( k1_xboole_0 = sk_H )
      | ( sk_E = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( ( k1_xboole_0 = sk_H )
      | ( k1_xboole_0 = sk_G )
      | ( k1_xboole_0 = sk_F )
      | ( k1_xboole_0 = sk_E ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('95',plain,
    ( ( ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ k1_xboole_0 ) )
      | ( k1_xboole_0 = sk_E )
      | ( k1_xboole_0 = sk_F )
      | ( k1_xboole_0 = sk_G ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( k4_zfmisc_1 @ X42 @ X43 @ X44 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('97',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t60_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( ( r2_hidden @ C @ B )
          & ( A != C ) )
        | ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
          = ( k1_tarski @ A ) ) ) ) )).

thf('98',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ( X10 != X12 )
      | ( ( k3_xboole_0 @ ( k2_tarski @ X10 @ X12 ) @ X11 )
        = ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t60_zfmisc_1])).

thf('99',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ ( k2_tarski @ X12 @ X12 ) @ X11 )
        = ( k1_tarski @ X12 ) )
      | ~ ( r2_hidden @ X12 @ X11 ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k3_xboole_0 @ ( k2_tarski @ ( sk_B @ X0 ) @ ( sk_B @ X0 ) ) @ X0 )
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['97','99'])).

thf('101',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('102',plain,
    ( ( ( k1_tarski @ ( sk_B @ k1_xboole_0 ) )
      = k1_xboole_0 )
    | ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(l35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('104',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X7 ) @ X9 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf(t67_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('106',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X13 ) @ X14 )
       != ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t67_zfmisc_1])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_B @ X0 ) @ X0 )
      | ( k1_xboole_0
       != ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X13: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X13 ) @ X15 )
        = ( k1_tarski @ X13 ) )
      | ( r2_hidden @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t67_zfmisc_1])).

thf('111',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X7 ) @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != k1_xboole_0 )
      | ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k1_tarski @ X0 )
       != k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ ( sk_B @ X0 ) ) ) ),
    inference(clc,[status(thm)],['109','113'])).

thf('115',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['102','114'])).

thf('116',plain,
    ( ( ( k1_xboole_0 = sk_E )
      | ( k1_xboole_0 = sk_F )
      | ( k1_xboole_0 = sk_G ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(demod,[status(thm)],['95','96','115'])).

thf('117',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('118',plain,
    ( ( ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ k1_xboole_0 @ sk_H ) )
      | ( k1_xboole_0 = sk_F )
      | ( k1_xboole_0 = sk_E ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X42: $i,X43: $i,X44: $i,X46: $i] :
      ( ( X44 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X42 @ X43 @ X44 @ X46 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('120',plain,(
    ! [X42: $i,X43: $i,X46: $i] :
      ( ( k4_zfmisc_1 @ X42 @ X43 @ k1_xboole_0 @ X46 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['102','114'])).

thf('122',plain,
    ( ( ( k1_xboole_0 = sk_F )
      | ( k1_xboole_0 = sk_E ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(demod,[status(thm)],['118','120','121'])).

thf('123',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('124',plain,
    ( ( ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ k1_xboole_0 @ sk_G @ sk_H ) )
      | ( k1_xboole_0 = sk_E ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X42: $i,X43: $i,X44: $i,X46: $i] :
      ( ( X43 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X42 @ X43 @ X44 @ X46 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('126',plain,(
    ! [X42: $i,X44: $i,X46: $i] :
      ( ( k4_zfmisc_1 @ X42 @ k1_xboole_0 @ X44 @ X46 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['102','114'])).

thf('128',plain,
    ( ( k1_xboole_0 = sk_E )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(demod,[status(thm)],['124','126','127'])).

thf('129',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('130',plain,
    ( ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ k1_xboole_0 @ sk_F @ sk_G @ sk_H ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X43: $i,X44: $i,X46: $i] :
      ( ( k4_zfmisc_1 @ k1_xboole_0 @ X43 @ X44 @ X46 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('132',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['102','114'])).

thf('133',plain,(
    r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ),
    inference(demod,[status(thm)],['130','131','132'])).

thf('134',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('135',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( X47 = k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( X49 = k1_xboole_0 )
      | ( ( k10_mcart_1 @ X47 @ X48 @ X49 @ X51 @ X50 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X50 ) ) )
      | ~ ( m1_subset_1 @ X50 @ ( k4_zfmisc_1 @ X47 @ X48 @ X49 @ X51 ) )
      | ( X51 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('136',plain,
    ( ( sk_H = k1_xboole_0 )
    | ( ( k10_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) )
    | ( sk_G = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf(dt_k10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ( m1_subset_1 @ ( k10_mcart_1 @ A @ B @ C @ D @ E ) @ C ) ) )).

thf('138',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( m1_subset_1 @ ( k10_mcart_1 @ X22 @ X23 @ X24 @ X25 @ X26 ) @ X24 )
      | ~ ( m1_subset_1 @ X26 @ ( k4_zfmisc_1 @ X22 @ X23 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_mcart_1])).

thf('139',plain,(
    m1_subset_1 @ ( k10_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) @ sk_G ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ X17 )
      | ( r2_hidden @ X16 @ X17 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('141',plain,
    ( ( v1_xboole_0 @ sk_G )
    | ( r2_hidden @ ( k10_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('143',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('144',plain,(
    ! [X42: $i,X43: $i,X46: $i] :
      ( ( k4_zfmisc_1 @ X42 @ X43 @ k1_xboole_0 @ X46 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['119'])).

thf('145',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['143','144'])).

thf('146',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('147',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_G ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_G ) ) ),
    inference('sup-',[status(thm)],['142','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_G )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,(
    ~ ( v1_xboole_0 @ sk_G ) ),
    inference(condensation,[status(thm)],['149'])).

thf('151',plain,(
    r2_hidden @ ( k10_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) @ sk_G ),
    inference(clc,[status(thm)],['141','150'])).

thf('152',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) @ sk_G )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['136','151'])).

thf('153',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( X47 = k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( X49 = k1_xboole_0 )
      | ( ( k10_mcart_1 @ X47 @ X48 @ X49 @ X51 @ X50 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X50 ) ) )
      | ~ ( m1_subset_1 @ X50 @ ( k4_zfmisc_1 @ X47 @ X48 @ X49 @ X51 ) )
      | ( X51 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('155',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,
    ( ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference(split,[status(esa)],['30'])).

thf('157',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) @ sk_G )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,
    ( ( ( sk_H = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['152','157'])).

thf('159',plain,
    ( ( k3_xboole_0 @ sk_H @ sk_D )
    = sk_H ),
    inference('sup-',[status(thm)],['60','61'])).

thf('160',plain,
    ( ( ( ( k3_xboole_0 @ sk_H @ k1_xboole_0 )
        = sk_H )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup+',[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('162',plain,
    ( ( ( k1_xboole_0 = sk_H )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference(demod,[status(thm)],['160','161'])).

thf('163',plain,
    ( ( ( sk_G = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( k1_xboole_0 = sk_H ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,
    ( ( k3_xboole_0 @ sk_G @ sk_C )
    = sk_G ),
    inference('sup-',[status(thm)],['69','70'])).

thf('165',plain,
    ( ( ( ( k3_xboole_0 @ sk_G @ k1_xboole_0 )
        = sk_G )
      | ( k1_xboole_0 = sk_H )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup+',[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('167',plain,
    ( ( ( k1_xboole_0 = sk_G )
      | ( k1_xboole_0 = sk_H )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,
    ( ( ( sk_F = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( k1_xboole_0 = sk_H )
      | ( k1_xboole_0 = sk_G ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,
    ( ( k3_xboole_0 @ sk_F @ sk_B_1 )
    = sk_F ),
    inference('sup-',[status(thm)],['78','79'])).

thf('170',plain,
    ( ( ( ( k3_xboole_0 @ sk_F @ k1_xboole_0 )
        = sk_F )
      | ( k1_xboole_0 = sk_G )
      | ( k1_xboole_0 = sk_H )
      | ( sk_A = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup+',[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('172',plain,
    ( ( ( k1_xboole_0 = sk_F )
      | ( k1_xboole_0 = sk_G )
      | ( k1_xboole_0 = sk_H )
      | ( sk_A = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference(demod,[status(thm)],['170','171'])).

thf('173',plain,
    ( ( ( sk_E = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( k1_xboole_0 = sk_H )
      | ( k1_xboole_0 = sk_G )
      | ( k1_xboole_0 = sk_F ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,
    ( ( k3_xboole_0 @ sk_E @ sk_A )
    = sk_E ),
    inference('sup-',[status(thm)],['87','88'])).

thf('175',plain,
    ( ( ( ( k3_xboole_0 @ sk_E @ k1_xboole_0 )
        = sk_E )
      | ( k1_xboole_0 = sk_F )
      | ( k1_xboole_0 = sk_G )
      | ( k1_xboole_0 = sk_H )
      | ( sk_E = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup+',[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('177',plain,
    ( ( ( k1_xboole_0 = sk_E )
      | ( k1_xboole_0 = sk_F )
      | ( k1_xboole_0 = sk_G )
      | ( k1_xboole_0 = sk_H )
      | ( sk_E = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference(demod,[status(thm)],['175','176'])).

thf('178',plain,
    ( ( ( k1_xboole_0 = sk_H )
      | ( k1_xboole_0 = sk_G )
      | ( k1_xboole_0 = sk_F )
      | ( k1_xboole_0 = sk_E ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference(simplify,[status(thm)],['177'])).

thf('179',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('180',plain,
    ( ( ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ k1_xboole_0 ) )
      | ( k1_xboole_0 = sk_E )
      | ( k1_xboole_0 = sk_F )
      | ( k1_xboole_0 = sk_G ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( k4_zfmisc_1 @ X42 @ X43 @ X44 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('182',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['102','114'])).

thf('183',plain,
    ( ( ( k1_xboole_0 = sk_E )
      | ( k1_xboole_0 = sk_F )
      | ( k1_xboole_0 = sk_G ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference(demod,[status(thm)],['180','181','182'])).

thf('184',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('185',plain,
    ( ( ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ k1_xboole_0 @ sk_H ) )
      | ( k1_xboole_0 = sk_F )
      | ( k1_xboole_0 = sk_E ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    ! [X42: $i,X43: $i,X46: $i] :
      ( ( k4_zfmisc_1 @ X42 @ X43 @ k1_xboole_0 @ X46 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['119'])).

thf('187',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['102','114'])).

thf('188',plain,
    ( ( ( k1_xboole_0 = sk_F )
      | ( k1_xboole_0 = sk_E ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference(demod,[status(thm)],['185','186','187'])).

thf('189',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('190',plain,
    ( ( ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ k1_xboole_0 @ sk_G @ sk_H ) )
      | ( k1_xboole_0 = sk_E ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X42: $i,X44: $i,X46: $i] :
      ( ( k4_zfmisc_1 @ X42 @ k1_xboole_0 @ X44 @ X46 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['125'])).

thf('192',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['102','114'])).

thf('193',plain,
    ( ( k1_xboole_0 = sk_E )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference(demod,[status(thm)],['190','191','192'])).

thf('194',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('195',plain,
    ( ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ k1_xboole_0 @ sk_F @ sk_G @ sk_H ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X43: $i,X44: $i,X46: $i] :
      ( ( k4_zfmisc_1 @ k1_xboole_0 @ X43 @ X44 @ X46 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('197',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['102','114'])).

thf('198',plain,(
    r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ),
    inference(demod,[status(thm)],['195','196','197'])).

thf('199',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('200',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( X47 = k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( X49 = k1_xboole_0 )
      | ( ( k9_mcart_1 @ X47 @ X48 @ X49 @ X51 @ X50 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ X50 ) ) ) )
      | ~ ( m1_subset_1 @ X50 @ ( k4_zfmisc_1 @ X47 @ X48 @ X49 @ X51 ) )
      | ( X51 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('201',plain,
    ( ( sk_H = k1_xboole_0 )
    | ( ( k9_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) )
    | ( sk_G = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf(dt_k9_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ( m1_subset_1 @ ( k9_mcart_1 @ A @ B @ C @ D @ E ) @ B ) ) )).

thf('203',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( m1_subset_1 @ ( k9_mcart_1 @ X37 @ X38 @ X39 @ X40 @ X41 ) @ X38 )
      | ~ ( m1_subset_1 @ X41 @ ( k4_zfmisc_1 @ X37 @ X38 @ X39 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_mcart_1])).

thf('204',plain,(
    m1_subset_1 @ ( k9_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) @ sk_F ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ X17 )
      | ( r2_hidden @ X16 @ X17 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('206',plain,
    ( ( v1_xboole_0 @ sk_F )
    | ( r2_hidden @ ( k9_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['204','205'])).

thf('207',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('208',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('209',plain,(
    ! [X42: $i,X44: $i,X46: $i] :
      ( ( k4_zfmisc_1 @ X42 @ k1_xboole_0 @ X44 @ X46 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['125'])).

thf('210',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X0 @ X2 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['208','209'])).

thf('211',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('212',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('213',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['207','212'])).

thf('214',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_F )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['213'])).

thf('215',plain,(
    ~ ( v1_xboole_0 @ sk_F ) ),
    inference(condensation,[status(thm)],['214'])).

thf('216',plain,(
    r2_hidden @ ( k9_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) @ sk_F ),
    inference(clc,[status(thm)],['206','215'])).

thf('217',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_F )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['201','216'])).

thf('218',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( X47 = k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( X49 = k1_xboole_0 )
      | ( ( k9_mcart_1 @ X47 @ X48 @ X49 @ X51 @ X50 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ X50 ) ) ) )
      | ~ ( m1_subset_1 @ X50 @ ( k4_zfmisc_1 @ X47 @ X48 @ X49 @ X51 ) )
      | ( X51 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('220',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['218','219'])).

thf('221',plain,
    ( ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference(split,[status(esa)],['30'])).

thf('222',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_F )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['220','221'])).

thf('223',plain,
    ( ( ( sk_H = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['217','222'])).

thf('224',plain,
    ( ( k3_xboole_0 @ sk_H @ sk_D )
    = sk_H ),
    inference('sup-',[status(thm)],['60','61'])).

thf('225',plain,
    ( ( ( ( k3_xboole_0 @ sk_H @ k1_xboole_0 )
        = sk_H )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup+',[status(thm)],['223','224'])).

thf('226',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('227',plain,
    ( ( ( k1_xboole_0 = sk_H )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 )
      | ( sk_H = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference(demod,[status(thm)],['225','226'])).

thf('228',plain,
    ( ( ( sk_G = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( k1_xboole_0 = sk_H ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference(simplify,[status(thm)],['227'])).

thf('229',plain,
    ( ( k3_xboole_0 @ sk_G @ sk_C )
    = sk_G ),
    inference('sup-',[status(thm)],['69','70'])).

thf('230',plain,
    ( ( ( ( k3_xboole_0 @ sk_G @ k1_xboole_0 )
        = sk_G )
      | ( k1_xboole_0 = sk_H )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup+',[status(thm)],['228','229'])).

thf('231',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('232',plain,
    ( ( ( k1_xboole_0 = sk_G )
      | ( k1_xboole_0 = sk_H )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 )
      | ( sk_G = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference(demod,[status(thm)],['230','231'])).

thf('233',plain,
    ( ( ( sk_F = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( k1_xboole_0 = sk_H )
      | ( k1_xboole_0 = sk_G ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference(simplify,[status(thm)],['232'])).

thf('234',plain,
    ( ( k3_xboole_0 @ sk_F @ sk_B_1 )
    = sk_F ),
    inference('sup-',[status(thm)],['78','79'])).

thf('235',plain,
    ( ( ( ( k3_xboole_0 @ sk_F @ k1_xboole_0 )
        = sk_F )
      | ( k1_xboole_0 = sk_G )
      | ( k1_xboole_0 = sk_H )
      | ( sk_A = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup+',[status(thm)],['233','234'])).

thf('236',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('237',plain,
    ( ( ( k1_xboole_0 = sk_F )
      | ( k1_xboole_0 = sk_G )
      | ( k1_xboole_0 = sk_H )
      | ( sk_A = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( sk_F = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference(demod,[status(thm)],['235','236'])).

thf('238',plain,
    ( ( ( sk_E = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( k1_xboole_0 = sk_H )
      | ( k1_xboole_0 = sk_G )
      | ( k1_xboole_0 = sk_F ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference(simplify,[status(thm)],['237'])).

thf('239',plain,
    ( ( k3_xboole_0 @ sk_E @ sk_A )
    = sk_E ),
    inference('sup-',[status(thm)],['87','88'])).

thf('240',plain,
    ( ( ( ( k3_xboole_0 @ sk_E @ k1_xboole_0 )
        = sk_E )
      | ( k1_xboole_0 = sk_F )
      | ( k1_xboole_0 = sk_G )
      | ( k1_xboole_0 = sk_H )
      | ( sk_E = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup+',[status(thm)],['238','239'])).

thf('241',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('242',plain,
    ( ( ( k1_xboole_0 = sk_E )
      | ( k1_xboole_0 = sk_F )
      | ( k1_xboole_0 = sk_G )
      | ( k1_xboole_0 = sk_H )
      | ( sk_E = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference(demod,[status(thm)],['240','241'])).

thf('243',plain,
    ( ( ( k1_xboole_0 = sk_H )
      | ( k1_xboole_0 = sk_G )
      | ( k1_xboole_0 = sk_F )
      | ( k1_xboole_0 = sk_E ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference(simplify,[status(thm)],['242'])).

thf('244',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('245',plain,
    ( ( ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ k1_xboole_0 ) )
      | ( k1_xboole_0 = sk_E )
      | ( k1_xboole_0 = sk_F )
      | ( k1_xboole_0 = sk_G ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['243','244'])).

thf('246',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( k4_zfmisc_1 @ X42 @ X43 @ X44 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('247',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['102','114'])).

thf('248',plain,
    ( ( ( k1_xboole_0 = sk_E )
      | ( k1_xboole_0 = sk_F )
      | ( k1_xboole_0 = sk_G ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference(demod,[status(thm)],['245','246','247'])).

thf('249',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('250',plain,
    ( ( ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ k1_xboole_0 @ sk_H ) )
      | ( k1_xboole_0 = sk_F )
      | ( k1_xboole_0 = sk_E ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['248','249'])).

thf('251',plain,(
    ! [X42: $i,X43: $i,X46: $i] :
      ( ( k4_zfmisc_1 @ X42 @ X43 @ k1_xboole_0 @ X46 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['119'])).

thf('252',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['102','114'])).

thf('253',plain,
    ( ( ( k1_xboole_0 = sk_F )
      | ( k1_xboole_0 = sk_E ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference(demod,[status(thm)],['250','251','252'])).

thf('254',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('255',plain,
    ( ( ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ k1_xboole_0 @ sk_G @ sk_H ) )
      | ( k1_xboole_0 = sk_E ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['253','254'])).

thf('256',plain,(
    ! [X42: $i,X44: $i,X46: $i] :
      ( ( k4_zfmisc_1 @ X42 @ k1_xboole_0 @ X44 @ X46 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['125'])).

thf('257',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['102','114'])).

thf('258',plain,
    ( ( k1_xboole_0 = sk_E )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference(demod,[status(thm)],['255','256','257'])).

thf('259',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('260',plain,
    ( ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ k1_xboole_0 @ sk_F @ sk_G @ sk_H ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['258','259'])).

thf('261',plain,(
    ! [X43: $i,X44: $i,X46: $i] :
      ( ( k4_zfmisc_1 @ k1_xboole_0 @ X43 @ X44 @ X46 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('262',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['102','114'])).

thf('263',plain,(
    r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ),
    inference(demod,[status(thm)],['260','261','262'])).

thf('264',plain,
    ( ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_E )
    | ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F )
    | ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G )
    | ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(split,[status(esa)],['30'])).

thf('265',plain,(
    ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['133','198','263','264'])).

thf('266',plain,(
    ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['31','265'])).

thf('267',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_E )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','266'])).

thf('268',plain,
    ( ( sk_H = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','267'])).

thf('269',plain,
    ( ( k3_xboole_0 @ sk_H @ sk_D )
    = sk_H ),
    inference('sup-',[status(thm)],['60','61'])).

thf('270',plain,
    ( ( ( k3_xboole_0 @ sk_H @ k1_xboole_0 )
      = sk_H )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['268','269'])).

thf('271',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('272',plain,
    ( ( k1_xboole_0 = sk_H )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 )
    | ( sk_H = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['270','271'])).

thf('273',plain,
    ( ( sk_G = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( k1_xboole_0 = sk_H ) ),
    inference(simplify,[status(thm)],['272'])).

thf('274',plain,
    ( ( k3_xboole_0 @ sk_G @ sk_C )
    = sk_G ),
    inference('sup-',[status(thm)],['69','70'])).

thf('275',plain,
    ( ( ( k3_xboole_0 @ sk_G @ k1_xboole_0 )
      = sk_G )
    | ( k1_xboole_0 = sk_H )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['273','274'])).

thf('276',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('277',plain,
    ( ( k1_xboole_0 = sk_G )
    | ( k1_xboole_0 = sk_H )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 )
    | ( sk_G = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['275','276'])).

thf('278',plain,
    ( ( sk_F = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( k1_xboole_0 = sk_H )
    | ( k1_xboole_0 = sk_G ) ),
    inference(simplify,[status(thm)],['277'])).

thf('279',plain,
    ( ( k3_xboole_0 @ sk_F @ sk_B_1 )
    = sk_F ),
    inference('sup-',[status(thm)],['78','79'])).

thf('280',plain,
    ( ( ( k3_xboole_0 @ sk_F @ k1_xboole_0 )
      = sk_F )
    | ( k1_xboole_0 = sk_G )
    | ( k1_xboole_0 = sk_H )
    | ( sk_A = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['278','279'])).

thf('281',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('282',plain,
    ( ( k1_xboole_0 = sk_F )
    | ( k1_xboole_0 = sk_G )
    | ( k1_xboole_0 = sk_H )
    | ( sk_A = k1_xboole_0 )
    | ( sk_E = k1_xboole_0 )
    | ( sk_F = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['280','281'])).

thf('283',plain,
    ( ( sk_E = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( k1_xboole_0 = sk_H )
    | ( k1_xboole_0 = sk_G )
    | ( k1_xboole_0 = sk_F ) ),
    inference(simplify,[status(thm)],['282'])).

thf('284',plain,
    ( ( k3_xboole_0 @ sk_E @ sk_A )
    = sk_E ),
    inference('sup-',[status(thm)],['87','88'])).

thf('285',plain,
    ( ( ( k3_xboole_0 @ sk_E @ k1_xboole_0 )
      = sk_E )
    | ( k1_xboole_0 = sk_F )
    | ( k1_xboole_0 = sk_G )
    | ( k1_xboole_0 = sk_H )
    | ( sk_E = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['283','284'])).

thf('286',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('287',plain,
    ( ( k1_xboole_0 = sk_E )
    | ( k1_xboole_0 = sk_F )
    | ( k1_xboole_0 = sk_G )
    | ( k1_xboole_0 = sk_H )
    | ( sk_E = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['285','286'])).

thf('288',plain,
    ( ( k1_xboole_0 = sk_H )
    | ( k1_xboole_0 = sk_G )
    | ( k1_xboole_0 = sk_F )
    | ( k1_xboole_0 = sk_E ) ),
    inference(simplify,[status(thm)],['287'])).

thf('289',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('290',plain,
    ( ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ k1_xboole_0 ) )
    | ( k1_xboole_0 = sk_E )
    | ( k1_xboole_0 = sk_F )
    | ( k1_xboole_0 = sk_G ) ),
    inference('sup-',[status(thm)],['288','289'])).

thf('291',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( k4_zfmisc_1 @ X42 @ X43 @ X44 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('292',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['102','114'])).

thf('293',plain,
    ( ( k1_xboole_0 = sk_E )
    | ( k1_xboole_0 = sk_F )
    | ( k1_xboole_0 = sk_G ) ),
    inference(demod,[status(thm)],['290','291','292'])).

thf('294',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('295',plain,
    ( ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ k1_xboole_0 @ sk_H ) )
    | ( k1_xboole_0 = sk_F )
    | ( k1_xboole_0 = sk_E ) ),
    inference('sup-',[status(thm)],['293','294'])).

thf('296',plain,(
    ! [X42: $i,X43: $i,X46: $i] :
      ( ( k4_zfmisc_1 @ X42 @ X43 @ k1_xboole_0 @ X46 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['119'])).

thf('297',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['102','114'])).

thf('298',plain,
    ( ( k1_xboole_0 = sk_F )
    | ( k1_xboole_0 = sk_E ) ),
    inference(demod,[status(thm)],['295','296','297'])).

thf('299',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('300',plain,
    ( ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ k1_xboole_0 @ sk_G @ sk_H ) )
    | ( k1_xboole_0 = sk_E ) ),
    inference('sup-',[status(thm)],['298','299'])).

thf('301',plain,(
    ! [X42: $i,X44: $i,X46: $i] :
      ( ( k4_zfmisc_1 @ X42 @ k1_xboole_0 @ X44 @ X46 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['125'])).

thf('302',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['102','114'])).

thf('303',plain,(
    k1_xboole_0 = sk_E ),
    inference(demod,[status(thm)],['300','301','302'])).

thf('304',plain,(
    ! [X43: $i,X44: $i,X46: $i] :
      ( ( k4_zfmisc_1 @ k1_xboole_0 @ X43 @ X44 @ X46 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('305',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['102','114'])).

thf('306',plain,(
    $false ),
    inference(demod,[status(thm)],['2','303','304','305'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vIAew4fagt
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:12:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.04/1.22  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.04/1.22  % Solved by: fo/fo7.sh
% 1.04/1.22  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.04/1.22  % done 1292 iterations in 0.755s
% 1.04/1.22  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.04/1.22  % SZS output start Refutation
% 1.04/1.22  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 1.04/1.22  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.04/1.22  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.04/1.22  thf(sk_H_type, type, sk_H: $i).
% 1.04/1.22  thf(sk_B_type, type, sk_B: $i > $i).
% 1.04/1.22  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.04/1.22  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.04/1.22  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.04/1.22  thf(k11_mcart_1_type, type, k11_mcart_1: $i > $i > $i > $i > $i > $i).
% 1.04/1.22  thf(sk_E_type, type, sk_E: $i).
% 1.04/1.22  thf(k8_mcart_1_type, type, k8_mcart_1: $i > $i > $i > $i > $i > $i).
% 1.04/1.22  thf(k9_mcart_1_type, type, k9_mcart_1: $i > $i > $i > $i > $i > $i).
% 1.04/1.22  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.04/1.22  thf(k10_mcart_1_type, type, k10_mcart_1: $i > $i > $i > $i > $i > $i).
% 1.04/1.22  thf(sk_I_type, type, sk_I: $i).
% 1.04/1.22  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 1.04/1.22  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.04/1.22  thf(sk_C_type, type, sk_C: $i).
% 1.04/1.22  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.04/1.22  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.04/1.22  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.04/1.22  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 1.04/1.22  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.04/1.22  thf(sk_D_type, type, sk_D: $i).
% 1.04/1.22  thf(sk_G_type, type, sk_G: $i).
% 1.04/1.22  thf(sk_A_type, type, sk_A: $i).
% 1.04/1.22  thf(sk_F_type, type, sk_F: $i).
% 1.04/1.22  thf(t87_mcart_1, conjecture,
% 1.04/1.22    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.04/1.22     ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ A ) ) =>
% 1.04/1.22       ( ![F:$i]:
% 1.04/1.22         ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ B ) ) =>
% 1.04/1.22           ( ![G:$i]:
% 1.04/1.22             ( ( m1_subset_1 @ G @ ( k1_zfmisc_1 @ C ) ) =>
% 1.04/1.22               ( ![H:$i]:
% 1.04/1.22                 ( ( m1_subset_1 @ H @ ( k1_zfmisc_1 @ D ) ) =>
% 1.04/1.22                   ( ![I:$i]:
% 1.04/1.22                     ( ( m1_subset_1 @ I @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 1.04/1.22                       ( ( r2_hidden @ I @ ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 1.04/1.22                         ( ( r2_hidden @ ( k8_mcart_1 @ A @ B @ C @ D @ I ) @ E ) & 
% 1.04/1.22                           ( r2_hidden @ ( k9_mcart_1 @ A @ B @ C @ D @ I ) @ F ) & 
% 1.04/1.22                           ( r2_hidden @
% 1.04/1.22                             ( k10_mcart_1 @ A @ B @ C @ D @ I ) @ G ) & 
% 1.04/1.22                           ( r2_hidden @
% 1.04/1.22                             ( k11_mcart_1 @ A @ B @ C @ D @ I ) @ H ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.04/1.22  thf(zf_stmt_0, negated_conjecture,
% 1.04/1.22    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.04/1.22        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ A ) ) =>
% 1.04/1.22          ( ![F:$i]:
% 1.04/1.22            ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ B ) ) =>
% 1.04/1.22              ( ![G:$i]:
% 1.04/1.22                ( ( m1_subset_1 @ G @ ( k1_zfmisc_1 @ C ) ) =>
% 1.04/1.22                  ( ![H:$i]:
% 1.04/1.22                    ( ( m1_subset_1 @ H @ ( k1_zfmisc_1 @ D ) ) =>
% 1.04/1.22                      ( ![I:$i]:
% 1.04/1.22                        ( ( m1_subset_1 @ I @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 1.04/1.22                          ( ( r2_hidden @ I @ ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 1.04/1.22                            ( ( r2_hidden @
% 1.04/1.22                                ( k8_mcart_1 @ A @ B @ C @ D @ I ) @ E ) & 
% 1.04/1.22                              ( r2_hidden @
% 1.04/1.22                                ( k9_mcart_1 @ A @ B @ C @ D @ I ) @ F ) & 
% 1.04/1.22                              ( r2_hidden @
% 1.04/1.22                                ( k10_mcart_1 @ A @ B @ C @ D @ I ) @ G ) & 
% 1.04/1.22                              ( r2_hidden @
% 1.04/1.22                                ( k11_mcart_1 @ A @ B @ C @ D @ I ) @ H ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.04/1.22    inference('cnf.neg', [status(esa)], [t87_mcart_1])).
% 1.04/1.22  thf('0', plain,
% 1.04/1.22      ((r2_hidden @ sk_I @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.04/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.22  thf(d1_xboole_0, axiom,
% 1.04/1.22    (![A:$i]:
% 1.04/1.22     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.04/1.22  thf('1', plain,
% 1.04/1.22      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.04/1.22      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.04/1.22  thf('2', plain,
% 1.04/1.22      (~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.04/1.22      inference('sup-', [status(thm)], ['0', '1'])).
% 1.04/1.22  thf('3', plain,
% 1.04/1.22      ((r2_hidden @ sk_I @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.04/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.22  thf(d2_subset_1, axiom,
% 1.04/1.22    (![A:$i,B:$i]:
% 1.04/1.22     ( ( ( v1_xboole_0 @ A ) =>
% 1.04/1.22         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.04/1.22       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.04/1.22         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.04/1.22  thf('4', plain,
% 1.04/1.22      (![X16 : $i, X17 : $i]:
% 1.04/1.22         (~ (r2_hidden @ X16 @ X17)
% 1.04/1.22          | (m1_subset_1 @ X16 @ X17)
% 1.04/1.22          | (v1_xboole_0 @ X17))),
% 1.04/1.22      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.04/1.22  thf('5', plain,
% 1.04/1.22      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.04/1.22      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.04/1.22  thf('6', plain,
% 1.04/1.22      (![X16 : $i, X17 : $i]:
% 1.04/1.22         ((m1_subset_1 @ X16 @ X17) | ~ (r2_hidden @ X16 @ X17))),
% 1.04/1.22      inference('clc', [status(thm)], ['4', '5'])).
% 1.04/1.22  thf('7', plain,
% 1.04/1.22      ((m1_subset_1 @ sk_I @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.04/1.22      inference('sup-', [status(thm)], ['3', '6'])).
% 1.04/1.22  thf(t61_mcart_1, axiom,
% 1.04/1.22    (![A:$i,B:$i,C:$i,D:$i]:
% 1.04/1.22     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.04/1.22          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 1.04/1.22          ( ~( ![E:$i]:
% 1.04/1.22               ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 1.04/1.22                 ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) =
% 1.04/1.22                     ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 1.04/1.22                   ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) =
% 1.04/1.22                     ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 1.04/1.22                   ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) =
% 1.04/1.22                     ( k2_mcart_1 @ ( k1_mcart_1 @ E ) ) ) & 
% 1.04/1.22                   ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( k2_mcart_1 @ E ) ) ) ) ) ) ) ))).
% 1.04/1.22  thf('8', plain,
% 1.04/1.22      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 1.04/1.22         (((X47) = (k1_xboole_0))
% 1.04/1.22          | ((X48) = (k1_xboole_0))
% 1.04/1.22          | ((X49) = (k1_xboole_0))
% 1.04/1.22          | ((k8_mcart_1 @ X47 @ X48 @ X49 @ X51 @ X50)
% 1.04/1.22              = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ X50))))
% 1.04/1.22          | ~ (m1_subset_1 @ X50 @ (k4_zfmisc_1 @ X47 @ X48 @ X49 @ X51))
% 1.04/1.22          | ((X51) = (k1_xboole_0)))),
% 1.04/1.22      inference('cnf', [status(esa)], [t61_mcart_1])).
% 1.04/1.22  thf('9', plain,
% 1.04/1.22      ((((sk_H) = (k1_xboole_0))
% 1.04/1.22        | ((k8_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I)
% 1.04/1.22            = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))))
% 1.04/1.22        | ((sk_G) = (k1_xboole_0))
% 1.04/1.22        | ((sk_F) = (k1_xboole_0))
% 1.04/1.22        | ((sk_E) = (k1_xboole_0)))),
% 1.04/1.22      inference('sup-', [status(thm)], ['7', '8'])).
% 1.04/1.22  thf('10', plain,
% 1.04/1.22      ((m1_subset_1 @ sk_I @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.04/1.22      inference('sup-', [status(thm)], ['3', '6'])).
% 1.04/1.22  thf(dt_k8_mcart_1, axiom,
% 1.04/1.22    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.04/1.22     ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 1.04/1.22       ( m1_subset_1 @ ( k8_mcart_1 @ A @ B @ C @ D @ E ) @ A ) ))).
% 1.04/1.22  thf('11', plain,
% 1.04/1.22      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 1.04/1.22         ((m1_subset_1 @ (k8_mcart_1 @ X32 @ X33 @ X34 @ X35 @ X36) @ X32)
% 1.04/1.22          | ~ (m1_subset_1 @ X36 @ (k4_zfmisc_1 @ X32 @ X33 @ X34 @ X35)))),
% 1.04/1.22      inference('cnf', [status(esa)], [dt_k8_mcart_1])).
% 1.04/1.22  thf('12', plain,
% 1.04/1.22      ((m1_subset_1 @ (k8_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I) @ sk_E)),
% 1.04/1.22      inference('sup-', [status(thm)], ['10', '11'])).
% 1.04/1.22  thf('13', plain,
% 1.04/1.22      (![X16 : $i, X17 : $i]:
% 1.04/1.22         (~ (m1_subset_1 @ X16 @ X17)
% 1.04/1.22          | (r2_hidden @ X16 @ X17)
% 1.04/1.22          | (v1_xboole_0 @ X17))),
% 1.04/1.22      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.04/1.22  thf('14', plain,
% 1.04/1.22      (((v1_xboole_0 @ sk_E)
% 1.04/1.22        | (r2_hidden @ (k8_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I) @ sk_E))),
% 1.04/1.22      inference('sup-', [status(thm)], ['12', '13'])).
% 1.04/1.22  thf(t6_boole, axiom,
% 1.04/1.22    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.04/1.22  thf('15', plain,
% 1.04/1.22      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X6))),
% 1.04/1.22      inference('cnf', [status(esa)], [t6_boole])).
% 1.04/1.22  thf('16', plain,
% 1.04/1.22      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X6))),
% 1.04/1.22      inference('cnf', [status(esa)], [t6_boole])).
% 1.04/1.22  thf(t55_mcart_1, axiom,
% 1.04/1.22    (![A:$i,B:$i,C:$i,D:$i]:
% 1.04/1.22     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.04/1.22         ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) ) <=>
% 1.04/1.22       ( ( k4_zfmisc_1 @ A @ B @ C @ D ) != ( k1_xboole_0 ) ) ))).
% 1.04/1.22  thf('17', plain,
% 1.04/1.22      (![X42 : $i, X43 : $i, X44 : $i, X46 : $i]:
% 1.04/1.22         (((X42) != (k1_xboole_0))
% 1.04/1.22          | ((k4_zfmisc_1 @ X42 @ X43 @ X44 @ X46) = (k1_xboole_0)))),
% 1.04/1.22      inference('cnf', [status(esa)], [t55_mcart_1])).
% 1.04/1.22  thf('18', plain,
% 1.04/1.22      (![X43 : $i, X44 : $i, X46 : $i]:
% 1.04/1.22         ((k4_zfmisc_1 @ k1_xboole_0 @ X43 @ X44 @ X46) = (k1_xboole_0))),
% 1.04/1.22      inference('simplify', [status(thm)], ['17'])).
% 1.04/1.22  thf('19', plain,
% 1.04/1.22      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.04/1.22         (((k4_zfmisc_1 @ X0 @ X3 @ X2 @ X1) = (k1_xboole_0))
% 1.04/1.22          | ~ (v1_xboole_0 @ X0))),
% 1.04/1.22      inference('sup+', [status(thm)], ['16', '18'])).
% 1.04/1.22  thf('20', plain,
% 1.04/1.22      (~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.04/1.22      inference('sup-', [status(thm)], ['0', '1'])).
% 1.04/1.22  thf('21', plain, ((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_E))),
% 1.04/1.22      inference('sup-', [status(thm)], ['19', '20'])).
% 1.04/1.22  thf('22', plain,
% 1.04/1.22      (![X0 : $i]:
% 1.04/1.22         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ sk_E))),
% 1.04/1.22      inference('sup-', [status(thm)], ['15', '21'])).
% 1.04/1.22  thf('23', plain,
% 1.04/1.22      (![X0 : $i]: (~ (v1_xboole_0 @ sk_E) | ~ (v1_xboole_0 @ X0))),
% 1.04/1.22      inference('simplify', [status(thm)], ['22'])).
% 1.04/1.22  thf('24', plain, (~ (v1_xboole_0 @ sk_E)),
% 1.04/1.22      inference('condensation', [status(thm)], ['23'])).
% 1.04/1.22  thf('25', plain,
% 1.04/1.22      ((r2_hidden @ (k8_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I) @ sk_E)),
% 1.04/1.22      inference('clc', [status(thm)], ['14', '24'])).
% 1.04/1.22  thf('26', plain,
% 1.04/1.22      (((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ sk_E)
% 1.04/1.22        | ((sk_E) = (k1_xboole_0))
% 1.04/1.22        | ((sk_F) = (k1_xboole_0))
% 1.04/1.22        | ((sk_G) = (k1_xboole_0))
% 1.04/1.22        | ((sk_H) = (k1_xboole_0)))),
% 1.04/1.22      inference('sup+', [status(thm)], ['9', '25'])).
% 1.04/1.22  thf('27', plain,
% 1.04/1.22      ((m1_subset_1 @ sk_I @ (k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))),
% 1.04/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.22  thf('28', plain,
% 1.04/1.22      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 1.04/1.22         (((X47) = (k1_xboole_0))
% 1.04/1.22          | ((X48) = (k1_xboole_0))
% 1.04/1.22          | ((X49) = (k1_xboole_0))
% 1.04/1.22          | ((k8_mcart_1 @ X47 @ X48 @ X49 @ X51 @ X50)
% 1.04/1.22              = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ X50))))
% 1.04/1.22          | ~ (m1_subset_1 @ X50 @ (k4_zfmisc_1 @ X47 @ X48 @ X49 @ X51))
% 1.04/1.22          | ((X51) = (k1_xboole_0)))),
% 1.04/1.22      inference('cnf', [status(esa)], [t61_mcart_1])).
% 1.04/1.22  thf('29', plain,
% 1.04/1.22      ((((sk_D) = (k1_xboole_0))
% 1.04/1.22        | ((k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I)
% 1.04/1.22            = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))))
% 1.04/1.22        | ((sk_C) = (k1_xboole_0))
% 1.04/1.22        | ((sk_B_1) = (k1_xboole_0))
% 1.04/1.22        | ((sk_A) = (k1_xboole_0)))),
% 1.04/1.22      inference('sup-', [status(thm)], ['27', '28'])).
% 1.04/1.22  thf('30', plain,
% 1.04/1.22      ((~ (r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_E)
% 1.04/1.22        | ~ (r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 1.04/1.22             sk_F)
% 1.04/1.22        | ~ (r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 1.04/1.22             sk_G)
% 1.04/1.22        | ~ (r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 1.04/1.22             sk_H))),
% 1.04/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.22  thf('31', plain,
% 1.04/1.22      ((~ (r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_E))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 1.04/1.22               sk_E)))),
% 1.04/1.22      inference('split', [status(esa)], ['30'])).
% 1.04/1.22  thf('32', plain,
% 1.04/1.22      ((m1_subset_1 @ sk_I @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.04/1.22      inference('sup-', [status(thm)], ['3', '6'])).
% 1.04/1.22  thf('33', plain,
% 1.04/1.22      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 1.04/1.22         (((X47) = (k1_xboole_0))
% 1.04/1.22          | ((X48) = (k1_xboole_0))
% 1.04/1.22          | ((X49) = (k1_xboole_0))
% 1.04/1.22          | ((k11_mcart_1 @ X47 @ X48 @ X49 @ X51 @ X50) = (k2_mcart_1 @ X50))
% 1.04/1.22          | ~ (m1_subset_1 @ X50 @ (k4_zfmisc_1 @ X47 @ X48 @ X49 @ X51))
% 1.04/1.22          | ((X51) = (k1_xboole_0)))),
% 1.04/1.22      inference('cnf', [status(esa)], [t61_mcart_1])).
% 1.04/1.22  thf('34', plain,
% 1.04/1.22      ((((sk_H) = (k1_xboole_0))
% 1.04/1.22        | ((k11_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I)
% 1.04/1.22            = (k2_mcart_1 @ sk_I))
% 1.04/1.22        | ((sk_G) = (k1_xboole_0))
% 1.04/1.22        | ((sk_F) = (k1_xboole_0))
% 1.04/1.22        | ((sk_E) = (k1_xboole_0)))),
% 1.04/1.22      inference('sup-', [status(thm)], ['32', '33'])).
% 1.04/1.22  thf('35', plain,
% 1.04/1.22      ((m1_subset_1 @ sk_I @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.04/1.22      inference('sup-', [status(thm)], ['3', '6'])).
% 1.04/1.22  thf(dt_k11_mcart_1, axiom,
% 1.04/1.22    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.04/1.22     ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 1.04/1.22       ( m1_subset_1 @ ( k11_mcart_1 @ A @ B @ C @ D @ E ) @ D ) ))).
% 1.04/1.22  thf('36', plain,
% 1.04/1.22      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 1.04/1.22         ((m1_subset_1 @ (k11_mcart_1 @ X27 @ X28 @ X29 @ X30 @ X31) @ X30)
% 1.04/1.22          | ~ (m1_subset_1 @ X31 @ (k4_zfmisc_1 @ X27 @ X28 @ X29 @ X30)))),
% 1.04/1.22      inference('cnf', [status(esa)], [dt_k11_mcart_1])).
% 1.04/1.22  thf('37', plain,
% 1.04/1.22      ((m1_subset_1 @ (k11_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I) @ sk_H)),
% 1.04/1.22      inference('sup-', [status(thm)], ['35', '36'])).
% 1.04/1.22  thf('38', plain,
% 1.04/1.22      (![X16 : $i, X17 : $i]:
% 1.04/1.22         (~ (m1_subset_1 @ X16 @ X17)
% 1.04/1.22          | (r2_hidden @ X16 @ X17)
% 1.04/1.22          | (v1_xboole_0 @ X17))),
% 1.04/1.22      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.04/1.22  thf('39', plain,
% 1.04/1.22      (((v1_xboole_0 @ sk_H)
% 1.04/1.22        | (r2_hidden @ (k11_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I) @ sk_H))),
% 1.04/1.22      inference('sup-', [status(thm)], ['37', '38'])).
% 1.04/1.22  thf('40', plain,
% 1.04/1.22      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X6))),
% 1.04/1.22      inference('cnf', [status(esa)], [t6_boole])).
% 1.04/1.22  thf('41', plain,
% 1.04/1.22      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X6))),
% 1.04/1.22      inference('cnf', [status(esa)], [t6_boole])).
% 1.04/1.22  thf('42', plain,
% 1.04/1.22      (![X42 : $i, X43 : $i, X44 : $i, X46 : $i]:
% 1.04/1.22         (((X46) != (k1_xboole_0))
% 1.04/1.22          | ((k4_zfmisc_1 @ X42 @ X43 @ X44 @ X46) = (k1_xboole_0)))),
% 1.04/1.22      inference('cnf', [status(esa)], [t55_mcart_1])).
% 1.04/1.22  thf('43', plain,
% 1.04/1.22      (![X42 : $i, X43 : $i, X44 : $i]:
% 1.04/1.22         ((k4_zfmisc_1 @ X42 @ X43 @ X44 @ k1_xboole_0) = (k1_xboole_0))),
% 1.04/1.22      inference('simplify', [status(thm)], ['42'])).
% 1.04/1.22  thf('44', plain,
% 1.04/1.22      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.04/1.22         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) = (k1_xboole_0))
% 1.04/1.22          | ~ (v1_xboole_0 @ X0))),
% 1.04/1.22      inference('sup+', [status(thm)], ['41', '43'])).
% 1.04/1.22  thf('45', plain,
% 1.04/1.22      (~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.04/1.22      inference('sup-', [status(thm)], ['0', '1'])).
% 1.04/1.22  thf('46', plain, ((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_H))),
% 1.04/1.22      inference('sup-', [status(thm)], ['44', '45'])).
% 1.04/1.22  thf('47', plain,
% 1.04/1.22      (![X0 : $i]:
% 1.04/1.22         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ sk_H))),
% 1.04/1.22      inference('sup-', [status(thm)], ['40', '46'])).
% 1.04/1.22  thf('48', plain,
% 1.04/1.22      (![X0 : $i]: (~ (v1_xboole_0 @ sk_H) | ~ (v1_xboole_0 @ X0))),
% 1.04/1.22      inference('simplify', [status(thm)], ['47'])).
% 1.04/1.22  thf('49', plain, (~ (v1_xboole_0 @ sk_H)),
% 1.04/1.22      inference('condensation', [status(thm)], ['48'])).
% 1.04/1.22  thf('50', plain,
% 1.04/1.22      ((r2_hidden @ (k11_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I) @ sk_H)),
% 1.04/1.22      inference('clc', [status(thm)], ['39', '49'])).
% 1.04/1.22  thf('51', plain,
% 1.04/1.22      (((r2_hidden @ (k2_mcart_1 @ sk_I) @ sk_H)
% 1.04/1.22        | ((sk_E) = (k1_xboole_0))
% 1.04/1.22        | ((sk_F) = (k1_xboole_0))
% 1.04/1.22        | ((sk_G) = (k1_xboole_0))
% 1.04/1.22        | ((sk_H) = (k1_xboole_0)))),
% 1.04/1.22      inference('sup+', [status(thm)], ['34', '50'])).
% 1.04/1.22  thf('52', plain,
% 1.04/1.22      ((m1_subset_1 @ sk_I @ (k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))),
% 1.04/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.22  thf('53', plain,
% 1.04/1.22      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 1.04/1.22         (((X47) = (k1_xboole_0))
% 1.04/1.22          | ((X48) = (k1_xboole_0))
% 1.04/1.22          | ((X49) = (k1_xboole_0))
% 1.04/1.22          | ((k11_mcart_1 @ X47 @ X48 @ X49 @ X51 @ X50) = (k2_mcart_1 @ X50))
% 1.04/1.22          | ~ (m1_subset_1 @ X50 @ (k4_zfmisc_1 @ X47 @ X48 @ X49 @ X51))
% 1.04/1.22          | ((X51) = (k1_xboole_0)))),
% 1.04/1.22      inference('cnf', [status(esa)], [t61_mcart_1])).
% 1.04/1.22  thf('54', plain,
% 1.04/1.22      ((((sk_D) = (k1_xboole_0))
% 1.04/1.22        | ((k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I)
% 1.04/1.22            = (k2_mcart_1 @ sk_I))
% 1.04/1.22        | ((sk_C) = (k1_xboole_0))
% 1.04/1.22        | ((sk_B_1) = (k1_xboole_0))
% 1.04/1.22        | ((sk_A) = (k1_xboole_0)))),
% 1.04/1.22      inference('sup-', [status(thm)], ['52', '53'])).
% 1.04/1.22  thf('55', plain,
% 1.04/1.22      ((~ (r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 1.04/1.22           sk_H))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ 
% 1.04/1.22               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_H)))),
% 1.04/1.22      inference('split', [status(esa)], ['30'])).
% 1.04/1.22  thf('56', plain,
% 1.04/1.22      (((~ (r2_hidden @ (k2_mcart_1 @ sk_I) @ sk_H)
% 1.04/1.22         | ((sk_A) = (k1_xboole_0))
% 1.04/1.22         | ((sk_B_1) = (k1_xboole_0))
% 1.04/1.22         | ((sk_C) = (k1_xboole_0))
% 1.04/1.22         | ((sk_D) = (k1_xboole_0))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ 
% 1.04/1.22               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_H)))),
% 1.04/1.22      inference('sup-', [status(thm)], ['54', '55'])).
% 1.04/1.22  thf('57', plain,
% 1.04/1.22      (((((sk_H) = (k1_xboole_0))
% 1.04/1.22         | ((sk_G) = (k1_xboole_0))
% 1.04/1.22         | ((sk_F) = (k1_xboole_0))
% 1.04/1.22         | ((sk_E) = (k1_xboole_0))
% 1.04/1.22         | ((sk_D) = (k1_xboole_0))
% 1.04/1.22         | ((sk_C) = (k1_xboole_0))
% 1.04/1.22         | ((sk_B_1) = (k1_xboole_0))
% 1.04/1.22         | ((sk_A) = (k1_xboole_0))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ 
% 1.04/1.22               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_H)))),
% 1.04/1.22      inference('sup-', [status(thm)], ['51', '56'])).
% 1.04/1.22  thf('58', plain, ((m1_subset_1 @ sk_H @ (k1_zfmisc_1 @ sk_D))),
% 1.04/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.22  thf(t3_subset, axiom,
% 1.04/1.22    (![A:$i,B:$i]:
% 1.04/1.22     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.04/1.22  thf('59', plain,
% 1.04/1.22      (![X19 : $i, X20 : $i]:
% 1.04/1.22         ((r1_tarski @ X19 @ X20) | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 1.04/1.22      inference('cnf', [status(esa)], [t3_subset])).
% 1.04/1.22  thf('60', plain, ((r1_tarski @ sk_H @ sk_D)),
% 1.04/1.22      inference('sup-', [status(thm)], ['58', '59'])).
% 1.04/1.22  thf(t28_xboole_1, axiom,
% 1.04/1.22    (![A:$i,B:$i]:
% 1.04/1.22     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.04/1.22  thf('61', plain,
% 1.04/1.22      (![X3 : $i, X4 : $i]:
% 1.04/1.22         (((k3_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_tarski @ X3 @ X4))),
% 1.04/1.22      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.04/1.22  thf('62', plain, (((k3_xboole_0 @ sk_H @ sk_D) = (sk_H))),
% 1.04/1.22      inference('sup-', [status(thm)], ['60', '61'])).
% 1.04/1.22  thf('63', plain,
% 1.04/1.22      (((((k3_xboole_0 @ sk_H @ k1_xboole_0) = (sk_H))
% 1.04/1.22         | ((sk_A) = (k1_xboole_0))
% 1.04/1.22         | ((sk_B_1) = (k1_xboole_0))
% 1.04/1.22         | ((sk_C) = (k1_xboole_0))
% 1.04/1.22         | ((sk_E) = (k1_xboole_0))
% 1.04/1.22         | ((sk_F) = (k1_xboole_0))
% 1.04/1.22         | ((sk_G) = (k1_xboole_0))
% 1.04/1.22         | ((sk_H) = (k1_xboole_0))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ 
% 1.04/1.22               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_H)))),
% 1.04/1.22      inference('sup+', [status(thm)], ['57', '62'])).
% 1.04/1.22  thf(t2_boole, axiom,
% 1.04/1.22    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.04/1.22  thf('64', plain,
% 1.04/1.22      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 1.04/1.22      inference('cnf', [status(esa)], [t2_boole])).
% 1.04/1.22  thf('65', plain,
% 1.04/1.22      (((((k1_xboole_0) = (sk_H))
% 1.04/1.22         | ((sk_A) = (k1_xboole_0))
% 1.04/1.22         | ((sk_B_1) = (k1_xboole_0))
% 1.04/1.22         | ((sk_C) = (k1_xboole_0))
% 1.04/1.22         | ((sk_E) = (k1_xboole_0))
% 1.04/1.22         | ((sk_F) = (k1_xboole_0))
% 1.04/1.22         | ((sk_G) = (k1_xboole_0))
% 1.04/1.22         | ((sk_H) = (k1_xboole_0))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ 
% 1.04/1.22               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_H)))),
% 1.04/1.22      inference('demod', [status(thm)], ['63', '64'])).
% 1.04/1.22  thf('66', plain,
% 1.04/1.22      (((((sk_G) = (k1_xboole_0))
% 1.04/1.22         | ((sk_F) = (k1_xboole_0))
% 1.04/1.22         | ((sk_E) = (k1_xboole_0))
% 1.04/1.22         | ((sk_C) = (k1_xboole_0))
% 1.04/1.22         | ((sk_B_1) = (k1_xboole_0))
% 1.04/1.22         | ((sk_A) = (k1_xboole_0))
% 1.04/1.22         | ((k1_xboole_0) = (sk_H))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ 
% 1.04/1.22               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_H)))),
% 1.04/1.22      inference('simplify', [status(thm)], ['65'])).
% 1.04/1.22  thf('67', plain, ((m1_subset_1 @ sk_G @ (k1_zfmisc_1 @ sk_C))),
% 1.04/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.22  thf('68', plain,
% 1.04/1.22      (![X19 : $i, X20 : $i]:
% 1.04/1.22         ((r1_tarski @ X19 @ X20) | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 1.04/1.22      inference('cnf', [status(esa)], [t3_subset])).
% 1.04/1.22  thf('69', plain, ((r1_tarski @ sk_G @ sk_C)),
% 1.04/1.22      inference('sup-', [status(thm)], ['67', '68'])).
% 1.04/1.22  thf('70', plain,
% 1.04/1.22      (![X3 : $i, X4 : $i]:
% 1.04/1.22         (((k3_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_tarski @ X3 @ X4))),
% 1.04/1.22      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.04/1.22  thf('71', plain, (((k3_xboole_0 @ sk_G @ sk_C) = (sk_G))),
% 1.04/1.22      inference('sup-', [status(thm)], ['69', '70'])).
% 1.04/1.22  thf('72', plain,
% 1.04/1.22      (((((k3_xboole_0 @ sk_G @ k1_xboole_0) = (sk_G))
% 1.04/1.22         | ((k1_xboole_0) = (sk_H))
% 1.04/1.22         | ((sk_A) = (k1_xboole_0))
% 1.04/1.22         | ((sk_B_1) = (k1_xboole_0))
% 1.04/1.22         | ((sk_E) = (k1_xboole_0))
% 1.04/1.22         | ((sk_F) = (k1_xboole_0))
% 1.04/1.22         | ((sk_G) = (k1_xboole_0))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ 
% 1.04/1.22               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_H)))),
% 1.04/1.22      inference('sup+', [status(thm)], ['66', '71'])).
% 1.04/1.22  thf('73', plain,
% 1.04/1.22      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 1.04/1.22      inference('cnf', [status(esa)], [t2_boole])).
% 1.04/1.22  thf('74', plain,
% 1.04/1.22      (((((k1_xboole_0) = (sk_G))
% 1.04/1.22         | ((k1_xboole_0) = (sk_H))
% 1.04/1.22         | ((sk_A) = (k1_xboole_0))
% 1.04/1.22         | ((sk_B_1) = (k1_xboole_0))
% 1.04/1.22         | ((sk_E) = (k1_xboole_0))
% 1.04/1.22         | ((sk_F) = (k1_xboole_0))
% 1.04/1.22         | ((sk_G) = (k1_xboole_0))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ 
% 1.04/1.22               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_H)))),
% 1.04/1.22      inference('demod', [status(thm)], ['72', '73'])).
% 1.04/1.22  thf('75', plain,
% 1.04/1.22      (((((sk_F) = (k1_xboole_0))
% 1.04/1.22         | ((sk_E) = (k1_xboole_0))
% 1.04/1.22         | ((sk_B_1) = (k1_xboole_0))
% 1.04/1.22         | ((sk_A) = (k1_xboole_0))
% 1.04/1.22         | ((k1_xboole_0) = (sk_H))
% 1.04/1.22         | ((k1_xboole_0) = (sk_G))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ 
% 1.04/1.22               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_H)))),
% 1.04/1.22      inference('simplify', [status(thm)], ['74'])).
% 1.04/1.22  thf('76', plain, ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ sk_B_1))),
% 1.04/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.22  thf('77', plain,
% 1.04/1.22      (![X19 : $i, X20 : $i]:
% 1.04/1.22         ((r1_tarski @ X19 @ X20) | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 1.04/1.22      inference('cnf', [status(esa)], [t3_subset])).
% 1.04/1.22  thf('78', plain, ((r1_tarski @ sk_F @ sk_B_1)),
% 1.04/1.22      inference('sup-', [status(thm)], ['76', '77'])).
% 1.04/1.22  thf('79', plain,
% 1.04/1.22      (![X3 : $i, X4 : $i]:
% 1.04/1.22         (((k3_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_tarski @ X3 @ X4))),
% 1.04/1.22      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.04/1.22  thf('80', plain, (((k3_xboole_0 @ sk_F @ sk_B_1) = (sk_F))),
% 1.04/1.22      inference('sup-', [status(thm)], ['78', '79'])).
% 1.04/1.22  thf('81', plain,
% 1.04/1.22      (((((k3_xboole_0 @ sk_F @ k1_xboole_0) = (sk_F))
% 1.04/1.22         | ((k1_xboole_0) = (sk_G))
% 1.04/1.22         | ((k1_xboole_0) = (sk_H))
% 1.04/1.22         | ((sk_A) = (k1_xboole_0))
% 1.04/1.22         | ((sk_E) = (k1_xboole_0))
% 1.04/1.22         | ((sk_F) = (k1_xboole_0))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ 
% 1.04/1.22               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_H)))),
% 1.04/1.22      inference('sup+', [status(thm)], ['75', '80'])).
% 1.04/1.22  thf('82', plain,
% 1.04/1.22      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 1.04/1.22      inference('cnf', [status(esa)], [t2_boole])).
% 1.04/1.22  thf('83', plain,
% 1.04/1.22      (((((k1_xboole_0) = (sk_F))
% 1.04/1.22         | ((k1_xboole_0) = (sk_G))
% 1.04/1.22         | ((k1_xboole_0) = (sk_H))
% 1.04/1.22         | ((sk_A) = (k1_xboole_0))
% 1.04/1.22         | ((sk_E) = (k1_xboole_0))
% 1.04/1.22         | ((sk_F) = (k1_xboole_0))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ 
% 1.04/1.22               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_H)))),
% 1.04/1.22      inference('demod', [status(thm)], ['81', '82'])).
% 1.04/1.22  thf('84', plain,
% 1.04/1.22      (((((sk_E) = (k1_xboole_0))
% 1.04/1.22         | ((sk_A) = (k1_xboole_0))
% 1.04/1.22         | ((k1_xboole_0) = (sk_H))
% 1.04/1.22         | ((k1_xboole_0) = (sk_G))
% 1.04/1.22         | ((k1_xboole_0) = (sk_F))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ 
% 1.04/1.22               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_H)))),
% 1.04/1.22      inference('simplify', [status(thm)], ['83'])).
% 1.04/1.22  thf('85', plain, ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ sk_A))),
% 1.04/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.22  thf('86', plain,
% 1.04/1.22      (![X19 : $i, X20 : $i]:
% 1.04/1.22         ((r1_tarski @ X19 @ X20) | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 1.04/1.22      inference('cnf', [status(esa)], [t3_subset])).
% 1.04/1.22  thf('87', plain, ((r1_tarski @ sk_E @ sk_A)),
% 1.04/1.22      inference('sup-', [status(thm)], ['85', '86'])).
% 1.04/1.22  thf('88', plain,
% 1.04/1.22      (![X3 : $i, X4 : $i]:
% 1.04/1.22         (((k3_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_tarski @ X3 @ X4))),
% 1.04/1.22      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.04/1.22  thf('89', plain, (((k3_xboole_0 @ sk_E @ sk_A) = (sk_E))),
% 1.04/1.22      inference('sup-', [status(thm)], ['87', '88'])).
% 1.04/1.22  thf('90', plain,
% 1.04/1.22      (((((k3_xboole_0 @ sk_E @ k1_xboole_0) = (sk_E))
% 1.04/1.22         | ((k1_xboole_0) = (sk_F))
% 1.04/1.22         | ((k1_xboole_0) = (sk_G))
% 1.04/1.22         | ((k1_xboole_0) = (sk_H))
% 1.04/1.22         | ((sk_E) = (k1_xboole_0))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ 
% 1.04/1.22               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_H)))),
% 1.04/1.22      inference('sup+', [status(thm)], ['84', '89'])).
% 1.04/1.22  thf('91', plain,
% 1.04/1.22      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 1.04/1.22      inference('cnf', [status(esa)], [t2_boole])).
% 1.04/1.22  thf('92', plain,
% 1.04/1.22      (((((k1_xboole_0) = (sk_E))
% 1.04/1.22         | ((k1_xboole_0) = (sk_F))
% 1.04/1.22         | ((k1_xboole_0) = (sk_G))
% 1.04/1.22         | ((k1_xboole_0) = (sk_H))
% 1.04/1.22         | ((sk_E) = (k1_xboole_0))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ 
% 1.04/1.22               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_H)))),
% 1.04/1.22      inference('demod', [status(thm)], ['90', '91'])).
% 1.04/1.22  thf('93', plain,
% 1.04/1.22      (((((k1_xboole_0) = (sk_H))
% 1.04/1.22         | ((k1_xboole_0) = (sk_G))
% 1.04/1.22         | ((k1_xboole_0) = (sk_F))
% 1.04/1.22         | ((k1_xboole_0) = (sk_E))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ 
% 1.04/1.22               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_H)))),
% 1.04/1.22      inference('simplify', [status(thm)], ['92'])).
% 1.04/1.22  thf('94', plain,
% 1.04/1.22      (~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.04/1.22      inference('sup-', [status(thm)], ['0', '1'])).
% 1.04/1.22  thf('95', plain,
% 1.04/1.22      (((~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ k1_xboole_0))
% 1.04/1.22         | ((k1_xboole_0) = (sk_E))
% 1.04/1.22         | ((k1_xboole_0) = (sk_F))
% 1.04/1.22         | ((k1_xboole_0) = (sk_G))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ 
% 1.04/1.22               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_H)))),
% 1.04/1.22      inference('sup-', [status(thm)], ['93', '94'])).
% 1.04/1.22  thf('96', plain,
% 1.04/1.22      (![X42 : $i, X43 : $i, X44 : $i]:
% 1.04/1.22         ((k4_zfmisc_1 @ X42 @ X43 @ X44 @ k1_xboole_0) = (k1_xboole_0))),
% 1.04/1.22      inference('simplify', [status(thm)], ['42'])).
% 1.04/1.22  thf('97', plain,
% 1.04/1.22      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.04/1.22      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.04/1.22  thf(t60_zfmisc_1, axiom,
% 1.04/1.22    (![A:$i,B:$i,C:$i]:
% 1.04/1.22     ( ( r2_hidden @ A @ B ) =>
% 1.04/1.22       ( ( ( r2_hidden @ C @ B ) & ( ( A ) != ( C ) ) ) | 
% 1.04/1.22         ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( k1_tarski @ A ) ) ) ))).
% 1.04/1.22  thf('98', plain,
% 1.04/1.22      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.04/1.22         (~ (r2_hidden @ X10 @ X11)
% 1.04/1.22          | ((X10) != (X12))
% 1.04/1.22          | ((k3_xboole_0 @ (k2_tarski @ X10 @ X12) @ X11) = (k1_tarski @ X10)))),
% 1.04/1.22      inference('cnf', [status(esa)], [t60_zfmisc_1])).
% 1.04/1.22  thf('99', plain,
% 1.04/1.22      (![X11 : $i, X12 : $i]:
% 1.04/1.22         (((k3_xboole_0 @ (k2_tarski @ X12 @ X12) @ X11) = (k1_tarski @ X12))
% 1.04/1.22          | ~ (r2_hidden @ X12 @ X11))),
% 1.04/1.22      inference('simplify', [status(thm)], ['98'])).
% 1.04/1.22  thf('100', plain,
% 1.04/1.22      (![X0 : $i]:
% 1.04/1.22         ((v1_xboole_0 @ X0)
% 1.04/1.22          | ((k3_xboole_0 @ (k2_tarski @ (sk_B @ X0) @ (sk_B @ X0)) @ X0)
% 1.04/1.22              = (k1_tarski @ (sk_B @ X0))))),
% 1.04/1.22      inference('sup-', [status(thm)], ['97', '99'])).
% 1.04/1.22  thf('101', plain,
% 1.04/1.22      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 1.04/1.22      inference('cnf', [status(esa)], [t2_boole])).
% 1.04/1.22  thf('102', plain,
% 1.04/1.22      ((((k1_tarski @ (sk_B @ k1_xboole_0)) = (k1_xboole_0))
% 1.04/1.22        | (v1_xboole_0 @ k1_xboole_0))),
% 1.04/1.22      inference('sup+', [status(thm)], ['100', '101'])).
% 1.04/1.22  thf('103', plain,
% 1.04/1.22      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.04/1.22      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.04/1.22  thf(l35_zfmisc_1, axiom,
% 1.04/1.22    (![A:$i,B:$i]:
% 1.04/1.22     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 1.04/1.22       ( r2_hidden @ A @ B ) ))).
% 1.04/1.22  thf('104', plain,
% 1.04/1.22      (![X7 : $i, X9 : $i]:
% 1.04/1.22         (((k4_xboole_0 @ (k1_tarski @ X7) @ X9) = (k1_xboole_0))
% 1.04/1.22          | ~ (r2_hidden @ X7 @ X9))),
% 1.04/1.22      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 1.04/1.22  thf('105', plain,
% 1.04/1.22      (![X0 : $i]:
% 1.04/1.22         ((v1_xboole_0 @ X0)
% 1.04/1.22          | ((k4_xboole_0 @ (k1_tarski @ (sk_B @ X0)) @ X0) = (k1_xboole_0)))),
% 1.04/1.22      inference('sup-', [status(thm)], ['103', '104'])).
% 1.04/1.22  thf(t67_zfmisc_1, axiom,
% 1.04/1.22    (![A:$i,B:$i]:
% 1.04/1.22     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 1.04/1.22       ( ~( r2_hidden @ A @ B ) ) ))).
% 1.04/1.22  thf('106', plain,
% 1.04/1.22      (![X13 : $i, X14 : $i]:
% 1.04/1.22         (~ (r2_hidden @ X13 @ X14)
% 1.04/1.22          | ((k4_xboole_0 @ (k1_tarski @ X13) @ X14) != (k1_tarski @ X13)))),
% 1.04/1.22      inference('cnf', [status(esa)], [t67_zfmisc_1])).
% 1.04/1.22  thf('107', plain,
% 1.04/1.22      (![X0 : $i]:
% 1.04/1.22         (((k1_xboole_0) != (k1_tarski @ (sk_B @ X0)))
% 1.04/1.22          | (v1_xboole_0 @ X0)
% 1.04/1.22          | ~ (r2_hidden @ (sk_B @ X0) @ X0))),
% 1.04/1.22      inference('sup-', [status(thm)], ['105', '106'])).
% 1.04/1.22  thf('108', plain,
% 1.04/1.22      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.04/1.22      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.04/1.22  thf('109', plain,
% 1.04/1.22      (![X0 : $i]:
% 1.04/1.22         (~ (r2_hidden @ (sk_B @ X0) @ X0)
% 1.04/1.22          | ((k1_xboole_0) != (k1_tarski @ (sk_B @ X0))))),
% 1.04/1.22      inference('clc', [status(thm)], ['107', '108'])).
% 1.04/1.22  thf('110', plain,
% 1.04/1.22      (![X13 : $i, X15 : $i]:
% 1.04/1.22         (((k4_xboole_0 @ (k1_tarski @ X13) @ X15) = (k1_tarski @ X13))
% 1.04/1.22          | (r2_hidden @ X13 @ X15))),
% 1.04/1.22      inference('cnf', [status(esa)], [t67_zfmisc_1])).
% 1.04/1.22  thf('111', plain,
% 1.04/1.22      (![X7 : $i, X8 : $i]:
% 1.04/1.22         ((r2_hidden @ X7 @ X8)
% 1.04/1.22          | ((k4_xboole_0 @ (k1_tarski @ X7) @ X8) != (k1_xboole_0)))),
% 1.04/1.22      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 1.04/1.22  thf('112', plain,
% 1.04/1.22      (![X0 : $i, X1 : $i]:
% 1.04/1.22         (((k1_tarski @ X0) != (k1_xboole_0))
% 1.04/1.22          | (r2_hidden @ X0 @ X1)
% 1.04/1.22          | (r2_hidden @ X0 @ X1))),
% 1.04/1.22      inference('sup-', [status(thm)], ['110', '111'])).
% 1.04/1.22  thf('113', plain,
% 1.04/1.22      (![X0 : $i, X1 : $i]:
% 1.04/1.22         ((r2_hidden @ X0 @ X1) | ((k1_tarski @ X0) != (k1_xboole_0)))),
% 1.04/1.22      inference('simplify', [status(thm)], ['112'])).
% 1.04/1.22  thf('114', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ (sk_B @ X0)))),
% 1.04/1.22      inference('clc', [status(thm)], ['109', '113'])).
% 1.04/1.22  thf('115', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.04/1.22      inference('clc', [status(thm)], ['102', '114'])).
% 1.04/1.22  thf('116', plain,
% 1.04/1.22      (((((k1_xboole_0) = (sk_E))
% 1.04/1.22         | ((k1_xboole_0) = (sk_F))
% 1.04/1.22         | ((k1_xboole_0) = (sk_G))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ 
% 1.04/1.22               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_H)))),
% 1.04/1.22      inference('demod', [status(thm)], ['95', '96', '115'])).
% 1.04/1.22  thf('117', plain,
% 1.04/1.22      (~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.04/1.22      inference('sup-', [status(thm)], ['0', '1'])).
% 1.04/1.22  thf('118', plain,
% 1.04/1.22      (((~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ sk_F @ k1_xboole_0 @ sk_H))
% 1.04/1.22         | ((k1_xboole_0) = (sk_F))
% 1.04/1.22         | ((k1_xboole_0) = (sk_E))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ 
% 1.04/1.22               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_H)))),
% 1.04/1.22      inference('sup-', [status(thm)], ['116', '117'])).
% 1.04/1.22  thf('119', plain,
% 1.04/1.22      (![X42 : $i, X43 : $i, X44 : $i, X46 : $i]:
% 1.04/1.22         (((X44) != (k1_xboole_0))
% 1.04/1.22          | ((k4_zfmisc_1 @ X42 @ X43 @ X44 @ X46) = (k1_xboole_0)))),
% 1.04/1.22      inference('cnf', [status(esa)], [t55_mcart_1])).
% 1.04/1.22  thf('120', plain,
% 1.04/1.22      (![X42 : $i, X43 : $i, X46 : $i]:
% 1.04/1.22         ((k4_zfmisc_1 @ X42 @ X43 @ k1_xboole_0 @ X46) = (k1_xboole_0))),
% 1.04/1.22      inference('simplify', [status(thm)], ['119'])).
% 1.04/1.22  thf('121', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.04/1.22      inference('clc', [status(thm)], ['102', '114'])).
% 1.04/1.22  thf('122', plain,
% 1.04/1.22      (((((k1_xboole_0) = (sk_F)) | ((k1_xboole_0) = (sk_E))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ 
% 1.04/1.22               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_H)))),
% 1.04/1.22      inference('demod', [status(thm)], ['118', '120', '121'])).
% 1.04/1.22  thf('123', plain,
% 1.04/1.22      (~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.04/1.22      inference('sup-', [status(thm)], ['0', '1'])).
% 1.04/1.22  thf('124', plain,
% 1.04/1.22      (((~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ k1_xboole_0 @ sk_G @ sk_H))
% 1.04/1.22         | ((k1_xboole_0) = (sk_E))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ 
% 1.04/1.22               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_H)))),
% 1.04/1.22      inference('sup-', [status(thm)], ['122', '123'])).
% 1.04/1.22  thf('125', plain,
% 1.04/1.22      (![X42 : $i, X43 : $i, X44 : $i, X46 : $i]:
% 1.04/1.22         (((X43) != (k1_xboole_0))
% 1.04/1.22          | ((k4_zfmisc_1 @ X42 @ X43 @ X44 @ X46) = (k1_xboole_0)))),
% 1.04/1.22      inference('cnf', [status(esa)], [t55_mcart_1])).
% 1.04/1.22  thf('126', plain,
% 1.04/1.22      (![X42 : $i, X44 : $i, X46 : $i]:
% 1.04/1.22         ((k4_zfmisc_1 @ X42 @ k1_xboole_0 @ X44 @ X46) = (k1_xboole_0))),
% 1.04/1.22      inference('simplify', [status(thm)], ['125'])).
% 1.04/1.22  thf('127', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.04/1.22      inference('clc', [status(thm)], ['102', '114'])).
% 1.04/1.22  thf('128', plain,
% 1.04/1.22      ((((k1_xboole_0) = (sk_E)))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ 
% 1.04/1.22               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_H)))),
% 1.04/1.22      inference('demod', [status(thm)], ['124', '126', '127'])).
% 1.04/1.22  thf('129', plain,
% 1.04/1.22      (~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.04/1.22      inference('sup-', [status(thm)], ['0', '1'])).
% 1.04/1.22  thf('130', plain,
% 1.04/1.22      ((~ (v1_xboole_0 @ (k4_zfmisc_1 @ k1_xboole_0 @ sk_F @ sk_G @ sk_H)))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ 
% 1.04/1.22               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_H)))),
% 1.04/1.22      inference('sup-', [status(thm)], ['128', '129'])).
% 1.04/1.22  thf('131', plain,
% 1.04/1.22      (![X43 : $i, X44 : $i, X46 : $i]:
% 1.04/1.22         ((k4_zfmisc_1 @ k1_xboole_0 @ X43 @ X44 @ X46) = (k1_xboole_0))),
% 1.04/1.22      inference('simplify', [status(thm)], ['17'])).
% 1.04/1.22  thf('132', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.04/1.22      inference('clc', [status(thm)], ['102', '114'])).
% 1.04/1.22  thf('133', plain,
% 1.04/1.22      (((r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_H))),
% 1.04/1.22      inference('demod', [status(thm)], ['130', '131', '132'])).
% 1.04/1.22  thf('134', plain,
% 1.04/1.22      ((m1_subset_1 @ sk_I @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.04/1.22      inference('sup-', [status(thm)], ['3', '6'])).
% 1.04/1.22  thf('135', plain,
% 1.04/1.22      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 1.04/1.22         (((X47) = (k1_xboole_0))
% 1.04/1.22          | ((X48) = (k1_xboole_0))
% 1.04/1.22          | ((X49) = (k1_xboole_0))
% 1.04/1.22          | ((k10_mcart_1 @ X47 @ X48 @ X49 @ X51 @ X50)
% 1.04/1.22              = (k2_mcart_1 @ (k1_mcart_1 @ X50)))
% 1.04/1.22          | ~ (m1_subset_1 @ X50 @ (k4_zfmisc_1 @ X47 @ X48 @ X49 @ X51))
% 1.04/1.22          | ((X51) = (k1_xboole_0)))),
% 1.04/1.22      inference('cnf', [status(esa)], [t61_mcart_1])).
% 1.04/1.22  thf('136', plain,
% 1.04/1.22      ((((sk_H) = (k1_xboole_0))
% 1.04/1.22        | ((k10_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I)
% 1.04/1.22            = (k2_mcart_1 @ (k1_mcart_1 @ sk_I)))
% 1.04/1.22        | ((sk_G) = (k1_xboole_0))
% 1.04/1.22        | ((sk_F) = (k1_xboole_0))
% 1.04/1.22        | ((sk_E) = (k1_xboole_0)))),
% 1.04/1.22      inference('sup-', [status(thm)], ['134', '135'])).
% 1.04/1.22  thf('137', plain,
% 1.04/1.22      ((m1_subset_1 @ sk_I @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.04/1.22      inference('sup-', [status(thm)], ['3', '6'])).
% 1.04/1.22  thf(dt_k10_mcart_1, axiom,
% 1.04/1.22    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.04/1.22     ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 1.04/1.22       ( m1_subset_1 @ ( k10_mcart_1 @ A @ B @ C @ D @ E ) @ C ) ))).
% 1.04/1.22  thf('138', plain,
% 1.04/1.22      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.04/1.22         ((m1_subset_1 @ (k10_mcart_1 @ X22 @ X23 @ X24 @ X25 @ X26) @ X24)
% 1.04/1.22          | ~ (m1_subset_1 @ X26 @ (k4_zfmisc_1 @ X22 @ X23 @ X24 @ X25)))),
% 1.04/1.22      inference('cnf', [status(esa)], [dt_k10_mcart_1])).
% 1.04/1.22  thf('139', plain,
% 1.04/1.22      ((m1_subset_1 @ (k10_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I) @ sk_G)),
% 1.04/1.22      inference('sup-', [status(thm)], ['137', '138'])).
% 1.04/1.22  thf('140', plain,
% 1.04/1.22      (![X16 : $i, X17 : $i]:
% 1.04/1.22         (~ (m1_subset_1 @ X16 @ X17)
% 1.04/1.22          | (r2_hidden @ X16 @ X17)
% 1.04/1.22          | (v1_xboole_0 @ X17))),
% 1.04/1.22      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.04/1.22  thf('141', plain,
% 1.04/1.22      (((v1_xboole_0 @ sk_G)
% 1.04/1.22        | (r2_hidden @ (k10_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I) @ sk_G))),
% 1.04/1.22      inference('sup-', [status(thm)], ['139', '140'])).
% 1.04/1.22  thf('142', plain,
% 1.04/1.22      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X6))),
% 1.04/1.22      inference('cnf', [status(esa)], [t6_boole])).
% 1.04/1.22  thf('143', plain,
% 1.04/1.22      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X6))),
% 1.04/1.22      inference('cnf', [status(esa)], [t6_boole])).
% 1.04/1.22  thf('144', plain,
% 1.04/1.22      (![X42 : $i, X43 : $i, X46 : $i]:
% 1.04/1.22         ((k4_zfmisc_1 @ X42 @ X43 @ k1_xboole_0 @ X46) = (k1_xboole_0))),
% 1.04/1.22      inference('simplify', [status(thm)], ['119'])).
% 1.04/1.22  thf('145', plain,
% 1.04/1.22      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.04/1.22         (((k4_zfmisc_1 @ X3 @ X2 @ X0 @ X1) = (k1_xboole_0))
% 1.04/1.22          | ~ (v1_xboole_0 @ X0))),
% 1.04/1.22      inference('sup+', [status(thm)], ['143', '144'])).
% 1.04/1.22  thf('146', plain,
% 1.04/1.22      (~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.04/1.22      inference('sup-', [status(thm)], ['0', '1'])).
% 1.04/1.22  thf('147', plain, ((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_G))),
% 1.04/1.22      inference('sup-', [status(thm)], ['145', '146'])).
% 1.04/1.22  thf('148', plain,
% 1.04/1.22      (![X0 : $i]:
% 1.04/1.22         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ sk_G))),
% 1.04/1.22      inference('sup-', [status(thm)], ['142', '147'])).
% 1.04/1.22  thf('149', plain,
% 1.04/1.22      (![X0 : $i]: (~ (v1_xboole_0 @ sk_G) | ~ (v1_xboole_0 @ X0))),
% 1.04/1.22      inference('simplify', [status(thm)], ['148'])).
% 1.04/1.22  thf('150', plain, (~ (v1_xboole_0 @ sk_G)),
% 1.04/1.22      inference('condensation', [status(thm)], ['149'])).
% 1.04/1.22  thf('151', plain,
% 1.04/1.22      ((r2_hidden @ (k10_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I) @ sk_G)),
% 1.04/1.22      inference('clc', [status(thm)], ['141', '150'])).
% 1.04/1.22  thf('152', plain,
% 1.04/1.22      (((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_I)) @ sk_G)
% 1.04/1.22        | ((sk_E) = (k1_xboole_0))
% 1.04/1.22        | ((sk_F) = (k1_xboole_0))
% 1.04/1.22        | ((sk_G) = (k1_xboole_0))
% 1.04/1.22        | ((sk_H) = (k1_xboole_0)))),
% 1.04/1.22      inference('sup+', [status(thm)], ['136', '151'])).
% 1.04/1.22  thf('153', plain,
% 1.04/1.22      ((m1_subset_1 @ sk_I @ (k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))),
% 1.04/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.22  thf('154', plain,
% 1.04/1.22      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 1.04/1.22         (((X47) = (k1_xboole_0))
% 1.04/1.22          | ((X48) = (k1_xboole_0))
% 1.04/1.22          | ((X49) = (k1_xboole_0))
% 1.04/1.22          | ((k10_mcart_1 @ X47 @ X48 @ X49 @ X51 @ X50)
% 1.04/1.22              = (k2_mcart_1 @ (k1_mcart_1 @ X50)))
% 1.04/1.22          | ~ (m1_subset_1 @ X50 @ (k4_zfmisc_1 @ X47 @ X48 @ X49 @ X51))
% 1.04/1.22          | ((X51) = (k1_xboole_0)))),
% 1.04/1.22      inference('cnf', [status(esa)], [t61_mcart_1])).
% 1.04/1.22  thf('155', plain,
% 1.04/1.22      ((((sk_D) = (k1_xboole_0))
% 1.04/1.22        | ((k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I)
% 1.04/1.22            = (k2_mcart_1 @ (k1_mcart_1 @ sk_I)))
% 1.04/1.22        | ((sk_C) = (k1_xboole_0))
% 1.04/1.22        | ((sk_B_1) = (k1_xboole_0))
% 1.04/1.22        | ((sk_A) = (k1_xboole_0)))),
% 1.04/1.22      inference('sup-', [status(thm)], ['153', '154'])).
% 1.04/1.22  thf('156', plain,
% 1.04/1.22      ((~ (r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 1.04/1.22           sk_G))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ 
% 1.04/1.22               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_G)))),
% 1.04/1.22      inference('split', [status(esa)], ['30'])).
% 1.04/1.22  thf('157', plain,
% 1.04/1.22      (((~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_I)) @ sk_G)
% 1.04/1.22         | ((sk_A) = (k1_xboole_0))
% 1.04/1.22         | ((sk_B_1) = (k1_xboole_0))
% 1.04/1.22         | ((sk_C) = (k1_xboole_0))
% 1.04/1.22         | ((sk_D) = (k1_xboole_0))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ 
% 1.04/1.22               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_G)))),
% 1.04/1.22      inference('sup-', [status(thm)], ['155', '156'])).
% 1.04/1.22  thf('158', plain,
% 1.04/1.22      (((((sk_H) = (k1_xboole_0))
% 1.04/1.22         | ((sk_G) = (k1_xboole_0))
% 1.04/1.22         | ((sk_F) = (k1_xboole_0))
% 1.04/1.22         | ((sk_E) = (k1_xboole_0))
% 1.04/1.22         | ((sk_D) = (k1_xboole_0))
% 1.04/1.22         | ((sk_C) = (k1_xboole_0))
% 1.04/1.22         | ((sk_B_1) = (k1_xboole_0))
% 1.04/1.22         | ((sk_A) = (k1_xboole_0))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ 
% 1.04/1.22               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_G)))),
% 1.04/1.22      inference('sup-', [status(thm)], ['152', '157'])).
% 1.04/1.22  thf('159', plain, (((k3_xboole_0 @ sk_H @ sk_D) = (sk_H))),
% 1.04/1.22      inference('sup-', [status(thm)], ['60', '61'])).
% 1.04/1.22  thf('160', plain,
% 1.04/1.22      (((((k3_xboole_0 @ sk_H @ k1_xboole_0) = (sk_H))
% 1.04/1.22         | ((sk_A) = (k1_xboole_0))
% 1.04/1.22         | ((sk_B_1) = (k1_xboole_0))
% 1.04/1.22         | ((sk_C) = (k1_xboole_0))
% 1.04/1.22         | ((sk_E) = (k1_xboole_0))
% 1.04/1.22         | ((sk_F) = (k1_xboole_0))
% 1.04/1.22         | ((sk_G) = (k1_xboole_0))
% 1.04/1.22         | ((sk_H) = (k1_xboole_0))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ 
% 1.04/1.22               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_G)))),
% 1.04/1.22      inference('sup+', [status(thm)], ['158', '159'])).
% 1.04/1.22  thf('161', plain,
% 1.04/1.22      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 1.04/1.22      inference('cnf', [status(esa)], [t2_boole])).
% 1.04/1.22  thf('162', plain,
% 1.04/1.22      (((((k1_xboole_0) = (sk_H))
% 1.04/1.22         | ((sk_A) = (k1_xboole_0))
% 1.04/1.22         | ((sk_B_1) = (k1_xboole_0))
% 1.04/1.22         | ((sk_C) = (k1_xboole_0))
% 1.04/1.22         | ((sk_E) = (k1_xboole_0))
% 1.04/1.22         | ((sk_F) = (k1_xboole_0))
% 1.04/1.22         | ((sk_G) = (k1_xboole_0))
% 1.04/1.22         | ((sk_H) = (k1_xboole_0))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ 
% 1.04/1.22               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_G)))),
% 1.04/1.22      inference('demod', [status(thm)], ['160', '161'])).
% 1.04/1.22  thf('163', plain,
% 1.04/1.22      (((((sk_G) = (k1_xboole_0))
% 1.04/1.22         | ((sk_F) = (k1_xboole_0))
% 1.04/1.22         | ((sk_E) = (k1_xboole_0))
% 1.04/1.22         | ((sk_C) = (k1_xboole_0))
% 1.04/1.22         | ((sk_B_1) = (k1_xboole_0))
% 1.04/1.22         | ((sk_A) = (k1_xboole_0))
% 1.04/1.22         | ((k1_xboole_0) = (sk_H))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ 
% 1.04/1.22               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_G)))),
% 1.04/1.22      inference('simplify', [status(thm)], ['162'])).
% 1.04/1.22  thf('164', plain, (((k3_xboole_0 @ sk_G @ sk_C) = (sk_G))),
% 1.04/1.22      inference('sup-', [status(thm)], ['69', '70'])).
% 1.04/1.22  thf('165', plain,
% 1.04/1.22      (((((k3_xboole_0 @ sk_G @ k1_xboole_0) = (sk_G))
% 1.04/1.22         | ((k1_xboole_0) = (sk_H))
% 1.04/1.22         | ((sk_A) = (k1_xboole_0))
% 1.04/1.22         | ((sk_B_1) = (k1_xboole_0))
% 1.04/1.22         | ((sk_E) = (k1_xboole_0))
% 1.04/1.22         | ((sk_F) = (k1_xboole_0))
% 1.04/1.22         | ((sk_G) = (k1_xboole_0))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ 
% 1.04/1.22               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_G)))),
% 1.04/1.22      inference('sup+', [status(thm)], ['163', '164'])).
% 1.04/1.22  thf('166', plain,
% 1.04/1.22      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 1.04/1.22      inference('cnf', [status(esa)], [t2_boole])).
% 1.04/1.22  thf('167', plain,
% 1.04/1.22      (((((k1_xboole_0) = (sk_G))
% 1.04/1.22         | ((k1_xboole_0) = (sk_H))
% 1.04/1.22         | ((sk_A) = (k1_xboole_0))
% 1.04/1.22         | ((sk_B_1) = (k1_xboole_0))
% 1.04/1.22         | ((sk_E) = (k1_xboole_0))
% 1.04/1.22         | ((sk_F) = (k1_xboole_0))
% 1.04/1.22         | ((sk_G) = (k1_xboole_0))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ 
% 1.04/1.22               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_G)))),
% 1.04/1.22      inference('demod', [status(thm)], ['165', '166'])).
% 1.04/1.22  thf('168', plain,
% 1.04/1.22      (((((sk_F) = (k1_xboole_0))
% 1.04/1.22         | ((sk_E) = (k1_xboole_0))
% 1.04/1.22         | ((sk_B_1) = (k1_xboole_0))
% 1.04/1.22         | ((sk_A) = (k1_xboole_0))
% 1.04/1.22         | ((k1_xboole_0) = (sk_H))
% 1.04/1.22         | ((k1_xboole_0) = (sk_G))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ 
% 1.04/1.22               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_G)))),
% 1.04/1.22      inference('simplify', [status(thm)], ['167'])).
% 1.04/1.22  thf('169', plain, (((k3_xboole_0 @ sk_F @ sk_B_1) = (sk_F))),
% 1.04/1.22      inference('sup-', [status(thm)], ['78', '79'])).
% 1.04/1.22  thf('170', plain,
% 1.04/1.22      (((((k3_xboole_0 @ sk_F @ k1_xboole_0) = (sk_F))
% 1.04/1.22         | ((k1_xboole_0) = (sk_G))
% 1.04/1.22         | ((k1_xboole_0) = (sk_H))
% 1.04/1.22         | ((sk_A) = (k1_xboole_0))
% 1.04/1.22         | ((sk_E) = (k1_xboole_0))
% 1.04/1.22         | ((sk_F) = (k1_xboole_0))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ 
% 1.04/1.22               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_G)))),
% 1.04/1.22      inference('sup+', [status(thm)], ['168', '169'])).
% 1.04/1.22  thf('171', plain,
% 1.04/1.22      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 1.04/1.22      inference('cnf', [status(esa)], [t2_boole])).
% 1.04/1.22  thf('172', plain,
% 1.04/1.22      (((((k1_xboole_0) = (sk_F))
% 1.04/1.22         | ((k1_xboole_0) = (sk_G))
% 1.04/1.22         | ((k1_xboole_0) = (sk_H))
% 1.04/1.22         | ((sk_A) = (k1_xboole_0))
% 1.04/1.22         | ((sk_E) = (k1_xboole_0))
% 1.04/1.22         | ((sk_F) = (k1_xboole_0))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ 
% 1.04/1.22               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_G)))),
% 1.04/1.22      inference('demod', [status(thm)], ['170', '171'])).
% 1.04/1.22  thf('173', plain,
% 1.04/1.22      (((((sk_E) = (k1_xboole_0))
% 1.04/1.22         | ((sk_A) = (k1_xboole_0))
% 1.04/1.22         | ((k1_xboole_0) = (sk_H))
% 1.04/1.22         | ((k1_xboole_0) = (sk_G))
% 1.04/1.22         | ((k1_xboole_0) = (sk_F))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ 
% 1.04/1.22               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_G)))),
% 1.04/1.22      inference('simplify', [status(thm)], ['172'])).
% 1.04/1.22  thf('174', plain, (((k3_xboole_0 @ sk_E @ sk_A) = (sk_E))),
% 1.04/1.22      inference('sup-', [status(thm)], ['87', '88'])).
% 1.04/1.22  thf('175', plain,
% 1.04/1.22      (((((k3_xboole_0 @ sk_E @ k1_xboole_0) = (sk_E))
% 1.04/1.22         | ((k1_xboole_0) = (sk_F))
% 1.04/1.22         | ((k1_xboole_0) = (sk_G))
% 1.04/1.22         | ((k1_xboole_0) = (sk_H))
% 1.04/1.22         | ((sk_E) = (k1_xboole_0))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ 
% 1.04/1.22               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_G)))),
% 1.04/1.22      inference('sup+', [status(thm)], ['173', '174'])).
% 1.04/1.22  thf('176', plain,
% 1.04/1.22      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 1.04/1.22      inference('cnf', [status(esa)], [t2_boole])).
% 1.04/1.22  thf('177', plain,
% 1.04/1.22      (((((k1_xboole_0) = (sk_E))
% 1.04/1.22         | ((k1_xboole_0) = (sk_F))
% 1.04/1.22         | ((k1_xboole_0) = (sk_G))
% 1.04/1.22         | ((k1_xboole_0) = (sk_H))
% 1.04/1.22         | ((sk_E) = (k1_xboole_0))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ 
% 1.04/1.22               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_G)))),
% 1.04/1.22      inference('demod', [status(thm)], ['175', '176'])).
% 1.04/1.22  thf('178', plain,
% 1.04/1.22      (((((k1_xboole_0) = (sk_H))
% 1.04/1.22         | ((k1_xboole_0) = (sk_G))
% 1.04/1.22         | ((k1_xboole_0) = (sk_F))
% 1.04/1.22         | ((k1_xboole_0) = (sk_E))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ 
% 1.04/1.22               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_G)))),
% 1.04/1.22      inference('simplify', [status(thm)], ['177'])).
% 1.04/1.22  thf('179', plain,
% 1.04/1.22      (~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.04/1.22      inference('sup-', [status(thm)], ['0', '1'])).
% 1.04/1.22  thf('180', plain,
% 1.04/1.22      (((~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ k1_xboole_0))
% 1.04/1.22         | ((k1_xboole_0) = (sk_E))
% 1.04/1.22         | ((k1_xboole_0) = (sk_F))
% 1.04/1.22         | ((k1_xboole_0) = (sk_G))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ 
% 1.04/1.22               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_G)))),
% 1.04/1.22      inference('sup-', [status(thm)], ['178', '179'])).
% 1.04/1.22  thf('181', plain,
% 1.04/1.22      (![X42 : $i, X43 : $i, X44 : $i]:
% 1.04/1.22         ((k4_zfmisc_1 @ X42 @ X43 @ X44 @ k1_xboole_0) = (k1_xboole_0))),
% 1.04/1.22      inference('simplify', [status(thm)], ['42'])).
% 1.04/1.22  thf('182', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.04/1.22      inference('clc', [status(thm)], ['102', '114'])).
% 1.04/1.22  thf('183', plain,
% 1.04/1.22      (((((k1_xboole_0) = (sk_E))
% 1.04/1.22         | ((k1_xboole_0) = (sk_F))
% 1.04/1.22         | ((k1_xboole_0) = (sk_G))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ 
% 1.04/1.22               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_G)))),
% 1.04/1.22      inference('demod', [status(thm)], ['180', '181', '182'])).
% 1.04/1.22  thf('184', plain,
% 1.04/1.22      (~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.04/1.22      inference('sup-', [status(thm)], ['0', '1'])).
% 1.04/1.22  thf('185', plain,
% 1.04/1.22      (((~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ sk_F @ k1_xboole_0 @ sk_H))
% 1.04/1.22         | ((k1_xboole_0) = (sk_F))
% 1.04/1.22         | ((k1_xboole_0) = (sk_E))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ 
% 1.04/1.22               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_G)))),
% 1.04/1.22      inference('sup-', [status(thm)], ['183', '184'])).
% 1.04/1.22  thf('186', plain,
% 1.04/1.22      (![X42 : $i, X43 : $i, X46 : $i]:
% 1.04/1.22         ((k4_zfmisc_1 @ X42 @ X43 @ k1_xboole_0 @ X46) = (k1_xboole_0))),
% 1.04/1.22      inference('simplify', [status(thm)], ['119'])).
% 1.04/1.22  thf('187', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.04/1.22      inference('clc', [status(thm)], ['102', '114'])).
% 1.04/1.22  thf('188', plain,
% 1.04/1.22      (((((k1_xboole_0) = (sk_F)) | ((k1_xboole_0) = (sk_E))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ 
% 1.04/1.22               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_G)))),
% 1.04/1.22      inference('demod', [status(thm)], ['185', '186', '187'])).
% 1.04/1.22  thf('189', plain,
% 1.04/1.22      (~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.04/1.22      inference('sup-', [status(thm)], ['0', '1'])).
% 1.04/1.22  thf('190', plain,
% 1.04/1.22      (((~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ k1_xboole_0 @ sk_G @ sk_H))
% 1.04/1.22         | ((k1_xboole_0) = (sk_E))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ 
% 1.04/1.22               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_G)))),
% 1.04/1.22      inference('sup-', [status(thm)], ['188', '189'])).
% 1.04/1.22  thf('191', plain,
% 1.04/1.22      (![X42 : $i, X44 : $i, X46 : $i]:
% 1.04/1.22         ((k4_zfmisc_1 @ X42 @ k1_xboole_0 @ X44 @ X46) = (k1_xboole_0))),
% 1.04/1.22      inference('simplify', [status(thm)], ['125'])).
% 1.04/1.22  thf('192', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.04/1.22      inference('clc', [status(thm)], ['102', '114'])).
% 1.04/1.22  thf('193', plain,
% 1.04/1.22      ((((k1_xboole_0) = (sk_E)))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ 
% 1.04/1.22               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_G)))),
% 1.04/1.22      inference('demod', [status(thm)], ['190', '191', '192'])).
% 1.04/1.22  thf('194', plain,
% 1.04/1.22      (~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.04/1.22      inference('sup-', [status(thm)], ['0', '1'])).
% 1.04/1.22  thf('195', plain,
% 1.04/1.22      ((~ (v1_xboole_0 @ (k4_zfmisc_1 @ k1_xboole_0 @ sk_F @ sk_G @ sk_H)))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ 
% 1.04/1.22               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_G)))),
% 1.04/1.22      inference('sup-', [status(thm)], ['193', '194'])).
% 1.04/1.22  thf('196', plain,
% 1.04/1.22      (![X43 : $i, X44 : $i, X46 : $i]:
% 1.04/1.22         ((k4_zfmisc_1 @ k1_xboole_0 @ X43 @ X44 @ X46) = (k1_xboole_0))),
% 1.04/1.22      inference('simplify', [status(thm)], ['17'])).
% 1.04/1.22  thf('197', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.04/1.22      inference('clc', [status(thm)], ['102', '114'])).
% 1.04/1.22  thf('198', plain,
% 1.04/1.22      (((r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_G))),
% 1.04/1.22      inference('demod', [status(thm)], ['195', '196', '197'])).
% 1.04/1.22  thf('199', plain,
% 1.04/1.22      ((m1_subset_1 @ sk_I @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.04/1.22      inference('sup-', [status(thm)], ['3', '6'])).
% 1.04/1.22  thf('200', plain,
% 1.04/1.22      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 1.04/1.22         (((X47) = (k1_xboole_0))
% 1.04/1.22          | ((X48) = (k1_xboole_0))
% 1.04/1.22          | ((X49) = (k1_xboole_0))
% 1.04/1.22          | ((k9_mcart_1 @ X47 @ X48 @ X49 @ X51 @ X50)
% 1.04/1.22              = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ X50))))
% 1.04/1.22          | ~ (m1_subset_1 @ X50 @ (k4_zfmisc_1 @ X47 @ X48 @ X49 @ X51))
% 1.04/1.22          | ((X51) = (k1_xboole_0)))),
% 1.04/1.22      inference('cnf', [status(esa)], [t61_mcart_1])).
% 1.04/1.22  thf('201', plain,
% 1.04/1.22      ((((sk_H) = (k1_xboole_0))
% 1.04/1.22        | ((k9_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I)
% 1.04/1.22            = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))))
% 1.04/1.22        | ((sk_G) = (k1_xboole_0))
% 1.04/1.22        | ((sk_F) = (k1_xboole_0))
% 1.04/1.22        | ((sk_E) = (k1_xboole_0)))),
% 1.04/1.22      inference('sup-', [status(thm)], ['199', '200'])).
% 1.04/1.22  thf('202', plain,
% 1.04/1.22      ((m1_subset_1 @ sk_I @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.04/1.22      inference('sup-', [status(thm)], ['3', '6'])).
% 1.04/1.22  thf(dt_k9_mcart_1, axiom,
% 1.04/1.22    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.04/1.22     ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 1.04/1.22       ( m1_subset_1 @ ( k9_mcart_1 @ A @ B @ C @ D @ E ) @ B ) ))).
% 1.04/1.22  thf('203', plain,
% 1.04/1.22      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 1.04/1.22         ((m1_subset_1 @ (k9_mcart_1 @ X37 @ X38 @ X39 @ X40 @ X41) @ X38)
% 1.04/1.22          | ~ (m1_subset_1 @ X41 @ (k4_zfmisc_1 @ X37 @ X38 @ X39 @ X40)))),
% 1.04/1.22      inference('cnf', [status(esa)], [dt_k9_mcart_1])).
% 1.04/1.22  thf('204', plain,
% 1.04/1.22      ((m1_subset_1 @ (k9_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I) @ sk_F)),
% 1.04/1.22      inference('sup-', [status(thm)], ['202', '203'])).
% 1.04/1.22  thf('205', plain,
% 1.04/1.22      (![X16 : $i, X17 : $i]:
% 1.04/1.22         (~ (m1_subset_1 @ X16 @ X17)
% 1.04/1.22          | (r2_hidden @ X16 @ X17)
% 1.04/1.22          | (v1_xboole_0 @ X17))),
% 1.04/1.22      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.04/1.22  thf('206', plain,
% 1.04/1.22      (((v1_xboole_0 @ sk_F)
% 1.04/1.22        | (r2_hidden @ (k9_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I) @ sk_F))),
% 1.04/1.22      inference('sup-', [status(thm)], ['204', '205'])).
% 1.04/1.22  thf('207', plain,
% 1.04/1.22      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X6))),
% 1.04/1.22      inference('cnf', [status(esa)], [t6_boole])).
% 1.04/1.22  thf('208', plain,
% 1.04/1.22      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X6))),
% 1.04/1.22      inference('cnf', [status(esa)], [t6_boole])).
% 1.04/1.22  thf('209', plain,
% 1.04/1.22      (![X42 : $i, X44 : $i, X46 : $i]:
% 1.04/1.22         ((k4_zfmisc_1 @ X42 @ k1_xboole_0 @ X44 @ X46) = (k1_xboole_0))),
% 1.04/1.22      inference('simplify', [status(thm)], ['125'])).
% 1.04/1.22  thf('210', plain,
% 1.04/1.22      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.04/1.22         (((k4_zfmisc_1 @ X3 @ X0 @ X2 @ X1) = (k1_xboole_0))
% 1.04/1.22          | ~ (v1_xboole_0 @ X0))),
% 1.04/1.22      inference('sup+', [status(thm)], ['208', '209'])).
% 1.04/1.22  thf('211', plain,
% 1.04/1.22      (~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.04/1.22      inference('sup-', [status(thm)], ['0', '1'])).
% 1.04/1.22  thf('212', plain, ((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_F))),
% 1.04/1.22      inference('sup-', [status(thm)], ['210', '211'])).
% 1.04/1.22  thf('213', plain,
% 1.04/1.22      (![X0 : $i]:
% 1.04/1.22         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ sk_F))),
% 1.04/1.22      inference('sup-', [status(thm)], ['207', '212'])).
% 1.04/1.22  thf('214', plain,
% 1.04/1.22      (![X0 : $i]: (~ (v1_xboole_0 @ sk_F) | ~ (v1_xboole_0 @ X0))),
% 1.04/1.22      inference('simplify', [status(thm)], ['213'])).
% 1.04/1.22  thf('215', plain, (~ (v1_xboole_0 @ sk_F)),
% 1.04/1.22      inference('condensation', [status(thm)], ['214'])).
% 1.04/1.22  thf('216', plain,
% 1.04/1.22      ((r2_hidden @ (k9_mcart_1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I) @ sk_F)),
% 1.04/1.22      inference('clc', [status(thm)], ['206', '215'])).
% 1.04/1.22  thf('217', plain,
% 1.04/1.22      (((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ sk_F)
% 1.04/1.22        | ((sk_E) = (k1_xboole_0))
% 1.04/1.22        | ((sk_F) = (k1_xboole_0))
% 1.04/1.22        | ((sk_G) = (k1_xboole_0))
% 1.04/1.22        | ((sk_H) = (k1_xboole_0)))),
% 1.04/1.22      inference('sup+', [status(thm)], ['201', '216'])).
% 1.04/1.22  thf('218', plain,
% 1.04/1.22      ((m1_subset_1 @ sk_I @ (k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))),
% 1.04/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.22  thf('219', plain,
% 1.04/1.22      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 1.04/1.22         (((X47) = (k1_xboole_0))
% 1.04/1.22          | ((X48) = (k1_xboole_0))
% 1.04/1.22          | ((X49) = (k1_xboole_0))
% 1.04/1.22          | ((k9_mcart_1 @ X47 @ X48 @ X49 @ X51 @ X50)
% 1.04/1.22              = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ X50))))
% 1.04/1.22          | ~ (m1_subset_1 @ X50 @ (k4_zfmisc_1 @ X47 @ X48 @ X49 @ X51))
% 1.04/1.22          | ((X51) = (k1_xboole_0)))),
% 1.04/1.22      inference('cnf', [status(esa)], [t61_mcart_1])).
% 1.04/1.22  thf('220', plain,
% 1.04/1.22      ((((sk_D) = (k1_xboole_0))
% 1.04/1.22        | ((k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I)
% 1.04/1.22            = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))))
% 1.04/1.22        | ((sk_C) = (k1_xboole_0))
% 1.04/1.22        | ((sk_B_1) = (k1_xboole_0))
% 1.04/1.22        | ((sk_A) = (k1_xboole_0)))),
% 1.04/1.22      inference('sup-', [status(thm)], ['218', '219'])).
% 1.04/1.22  thf('221', plain,
% 1.04/1.22      ((~ (r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_F))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 1.04/1.22               sk_F)))),
% 1.04/1.22      inference('split', [status(esa)], ['30'])).
% 1.04/1.22  thf('222', plain,
% 1.04/1.22      (((~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ 
% 1.04/1.22            sk_F)
% 1.04/1.22         | ((sk_A) = (k1_xboole_0))
% 1.04/1.22         | ((sk_B_1) = (k1_xboole_0))
% 1.04/1.22         | ((sk_C) = (k1_xboole_0))
% 1.04/1.22         | ((sk_D) = (k1_xboole_0))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 1.04/1.22               sk_F)))),
% 1.04/1.22      inference('sup-', [status(thm)], ['220', '221'])).
% 1.04/1.22  thf('223', plain,
% 1.04/1.22      (((((sk_H) = (k1_xboole_0))
% 1.04/1.22         | ((sk_G) = (k1_xboole_0))
% 1.04/1.22         | ((sk_F) = (k1_xboole_0))
% 1.04/1.22         | ((sk_E) = (k1_xboole_0))
% 1.04/1.22         | ((sk_D) = (k1_xboole_0))
% 1.04/1.22         | ((sk_C) = (k1_xboole_0))
% 1.04/1.22         | ((sk_B_1) = (k1_xboole_0))
% 1.04/1.22         | ((sk_A) = (k1_xboole_0))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 1.04/1.22               sk_F)))),
% 1.04/1.22      inference('sup-', [status(thm)], ['217', '222'])).
% 1.04/1.22  thf('224', plain, (((k3_xboole_0 @ sk_H @ sk_D) = (sk_H))),
% 1.04/1.22      inference('sup-', [status(thm)], ['60', '61'])).
% 1.04/1.22  thf('225', plain,
% 1.04/1.22      (((((k3_xboole_0 @ sk_H @ k1_xboole_0) = (sk_H))
% 1.04/1.22         | ((sk_A) = (k1_xboole_0))
% 1.04/1.22         | ((sk_B_1) = (k1_xboole_0))
% 1.04/1.22         | ((sk_C) = (k1_xboole_0))
% 1.04/1.22         | ((sk_E) = (k1_xboole_0))
% 1.04/1.22         | ((sk_F) = (k1_xboole_0))
% 1.04/1.22         | ((sk_G) = (k1_xboole_0))
% 1.04/1.22         | ((sk_H) = (k1_xboole_0))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 1.04/1.22               sk_F)))),
% 1.04/1.22      inference('sup+', [status(thm)], ['223', '224'])).
% 1.04/1.22  thf('226', plain,
% 1.04/1.22      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 1.04/1.22      inference('cnf', [status(esa)], [t2_boole])).
% 1.04/1.22  thf('227', plain,
% 1.04/1.22      (((((k1_xboole_0) = (sk_H))
% 1.04/1.22         | ((sk_A) = (k1_xboole_0))
% 1.04/1.22         | ((sk_B_1) = (k1_xboole_0))
% 1.04/1.22         | ((sk_C) = (k1_xboole_0))
% 1.04/1.22         | ((sk_E) = (k1_xboole_0))
% 1.04/1.22         | ((sk_F) = (k1_xboole_0))
% 1.04/1.22         | ((sk_G) = (k1_xboole_0))
% 1.04/1.22         | ((sk_H) = (k1_xboole_0))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 1.04/1.22               sk_F)))),
% 1.04/1.22      inference('demod', [status(thm)], ['225', '226'])).
% 1.04/1.22  thf('228', plain,
% 1.04/1.22      (((((sk_G) = (k1_xboole_0))
% 1.04/1.22         | ((sk_F) = (k1_xboole_0))
% 1.04/1.22         | ((sk_E) = (k1_xboole_0))
% 1.04/1.22         | ((sk_C) = (k1_xboole_0))
% 1.04/1.22         | ((sk_B_1) = (k1_xboole_0))
% 1.04/1.22         | ((sk_A) = (k1_xboole_0))
% 1.04/1.22         | ((k1_xboole_0) = (sk_H))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 1.04/1.22               sk_F)))),
% 1.04/1.22      inference('simplify', [status(thm)], ['227'])).
% 1.04/1.22  thf('229', plain, (((k3_xboole_0 @ sk_G @ sk_C) = (sk_G))),
% 1.04/1.22      inference('sup-', [status(thm)], ['69', '70'])).
% 1.04/1.22  thf('230', plain,
% 1.04/1.22      (((((k3_xboole_0 @ sk_G @ k1_xboole_0) = (sk_G))
% 1.04/1.22         | ((k1_xboole_0) = (sk_H))
% 1.04/1.22         | ((sk_A) = (k1_xboole_0))
% 1.04/1.22         | ((sk_B_1) = (k1_xboole_0))
% 1.04/1.22         | ((sk_E) = (k1_xboole_0))
% 1.04/1.22         | ((sk_F) = (k1_xboole_0))
% 1.04/1.22         | ((sk_G) = (k1_xboole_0))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 1.04/1.22               sk_F)))),
% 1.04/1.22      inference('sup+', [status(thm)], ['228', '229'])).
% 1.04/1.22  thf('231', plain,
% 1.04/1.22      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 1.04/1.22      inference('cnf', [status(esa)], [t2_boole])).
% 1.04/1.22  thf('232', plain,
% 1.04/1.22      (((((k1_xboole_0) = (sk_G))
% 1.04/1.22         | ((k1_xboole_0) = (sk_H))
% 1.04/1.22         | ((sk_A) = (k1_xboole_0))
% 1.04/1.22         | ((sk_B_1) = (k1_xboole_0))
% 1.04/1.22         | ((sk_E) = (k1_xboole_0))
% 1.04/1.22         | ((sk_F) = (k1_xboole_0))
% 1.04/1.22         | ((sk_G) = (k1_xboole_0))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 1.04/1.22               sk_F)))),
% 1.04/1.22      inference('demod', [status(thm)], ['230', '231'])).
% 1.04/1.22  thf('233', plain,
% 1.04/1.22      (((((sk_F) = (k1_xboole_0))
% 1.04/1.22         | ((sk_E) = (k1_xboole_0))
% 1.04/1.22         | ((sk_B_1) = (k1_xboole_0))
% 1.04/1.22         | ((sk_A) = (k1_xboole_0))
% 1.04/1.22         | ((k1_xboole_0) = (sk_H))
% 1.04/1.22         | ((k1_xboole_0) = (sk_G))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 1.04/1.22               sk_F)))),
% 1.04/1.22      inference('simplify', [status(thm)], ['232'])).
% 1.04/1.22  thf('234', plain, (((k3_xboole_0 @ sk_F @ sk_B_1) = (sk_F))),
% 1.04/1.22      inference('sup-', [status(thm)], ['78', '79'])).
% 1.04/1.22  thf('235', plain,
% 1.04/1.22      (((((k3_xboole_0 @ sk_F @ k1_xboole_0) = (sk_F))
% 1.04/1.22         | ((k1_xboole_0) = (sk_G))
% 1.04/1.22         | ((k1_xboole_0) = (sk_H))
% 1.04/1.22         | ((sk_A) = (k1_xboole_0))
% 1.04/1.22         | ((sk_E) = (k1_xboole_0))
% 1.04/1.22         | ((sk_F) = (k1_xboole_0))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 1.04/1.22               sk_F)))),
% 1.04/1.22      inference('sup+', [status(thm)], ['233', '234'])).
% 1.04/1.22  thf('236', plain,
% 1.04/1.22      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 1.04/1.22      inference('cnf', [status(esa)], [t2_boole])).
% 1.04/1.22  thf('237', plain,
% 1.04/1.22      (((((k1_xboole_0) = (sk_F))
% 1.04/1.22         | ((k1_xboole_0) = (sk_G))
% 1.04/1.22         | ((k1_xboole_0) = (sk_H))
% 1.04/1.22         | ((sk_A) = (k1_xboole_0))
% 1.04/1.22         | ((sk_E) = (k1_xboole_0))
% 1.04/1.22         | ((sk_F) = (k1_xboole_0))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 1.04/1.22               sk_F)))),
% 1.04/1.22      inference('demod', [status(thm)], ['235', '236'])).
% 1.04/1.22  thf('238', plain,
% 1.04/1.22      (((((sk_E) = (k1_xboole_0))
% 1.04/1.22         | ((sk_A) = (k1_xboole_0))
% 1.04/1.22         | ((k1_xboole_0) = (sk_H))
% 1.04/1.22         | ((k1_xboole_0) = (sk_G))
% 1.04/1.22         | ((k1_xboole_0) = (sk_F))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 1.04/1.22               sk_F)))),
% 1.04/1.22      inference('simplify', [status(thm)], ['237'])).
% 1.04/1.22  thf('239', plain, (((k3_xboole_0 @ sk_E @ sk_A) = (sk_E))),
% 1.04/1.22      inference('sup-', [status(thm)], ['87', '88'])).
% 1.04/1.22  thf('240', plain,
% 1.04/1.22      (((((k3_xboole_0 @ sk_E @ k1_xboole_0) = (sk_E))
% 1.04/1.22         | ((k1_xboole_0) = (sk_F))
% 1.04/1.22         | ((k1_xboole_0) = (sk_G))
% 1.04/1.22         | ((k1_xboole_0) = (sk_H))
% 1.04/1.22         | ((sk_E) = (k1_xboole_0))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 1.04/1.22               sk_F)))),
% 1.04/1.22      inference('sup+', [status(thm)], ['238', '239'])).
% 1.04/1.22  thf('241', plain,
% 1.04/1.22      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 1.04/1.22      inference('cnf', [status(esa)], [t2_boole])).
% 1.04/1.22  thf('242', plain,
% 1.04/1.22      (((((k1_xboole_0) = (sk_E))
% 1.04/1.22         | ((k1_xboole_0) = (sk_F))
% 1.04/1.22         | ((k1_xboole_0) = (sk_G))
% 1.04/1.22         | ((k1_xboole_0) = (sk_H))
% 1.04/1.22         | ((sk_E) = (k1_xboole_0))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 1.04/1.22               sk_F)))),
% 1.04/1.22      inference('demod', [status(thm)], ['240', '241'])).
% 1.04/1.22  thf('243', plain,
% 1.04/1.22      (((((k1_xboole_0) = (sk_H))
% 1.04/1.22         | ((k1_xboole_0) = (sk_G))
% 1.04/1.22         | ((k1_xboole_0) = (sk_F))
% 1.04/1.22         | ((k1_xboole_0) = (sk_E))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 1.04/1.22               sk_F)))),
% 1.04/1.22      inference('simplify', [status(thm)], ['242'])).
% 1.04/1.22  thf('244', plain,
% 1.04/1.22      (~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.04/1.22      inference('sup-', [status(thm)], ['0', '1'])).
% 1.04/1.22  thf('245', plain,
% 1.04/1.22      (((~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ k1_xboole_0))
% 1.04/1.22         | ((k1_xboole_0) = (sk_E))
% 1.04/1.22         | ((k1_xboole_0) = (sk_F))
% 1.04/1.22         | ((k1_xboole_0) = (sk_G))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 1.04/1.22               sk_F)))),
% 1.04/1.22      inference('sup-', [status(thm)], ['243', '244'])).
% 1.04/1.22  thf('246', plain,
% 1.04/1.22      (![X42 : $i, X43 : $i, X44 : $i]:
% 1.04/1.22         ((k4_zfmisc_1 @ X42 @ X43 @ X44 @ k1_xboole_0) = (k1_xboole_0))),
% 1.04/1.22      inference('simplify', [status(thm)], ['42'])).
% 1.04/1.22  thf('247', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.04/1.22      inference('clc', [status(thm)], ['102', '114'])).
% 1.04/1.22  thf('248', plain,
% 1.04/1.22      (((((k1_xboole_0) = (sk_E))
% 1.04/1.22         | ((k1_xboole_0) = (sk_F))
% 1.04/1.22         | ((k1_xboole_0) = (sk_G))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 1.04/1.22               sk_F)))),
% 1.04/1.22      inference('demod', [status(thm)], ['245', '246', '247'])).
% 1.04/1.22  thf('249', plain,
% 1.04/1.22      (~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.04/1.22      inference('sup-', [status(thm)], ['0', '1'])).
% 1.04/1.22  thf('250', plain,
% 1.04/1.22      (((~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ sk_F @ k1_xboole_0 @ sk_H))
% 1.04/1.22         | ((k1_xboole_0) = (sk_F))
% 1.04/1.22         | ((k1_xboole_0) = (sk_E))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 1.04/1.22               sk_F)))),
% 1.04/1.22      inference('sup-', [status(thm)], ['248', '249'])).
% 1.04/1.22  thf('251', plain,
% 1.04/1.22      (![X42 : $i, X43 : $i, X46 : $i]:
% 1.04/1.22         ((k4_zfmisc_1 @ X42 @ X43 @ k1_xboole_0 @ X46) = (k1_xboole_0))),
% 1.04/1.22      inference('simplify', [status(thm)], ['119'])).
% 1.04/1.22  thf('252', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.04/1.22      inference('clc', [status(thm)], ['102', '114'])).
% 1.04/1.22  thf('253', plain,
% 1.04/1.22      (((((k1_xboole_0) = (sk_F)) | ((k1_xboole_0) = (sk_E))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 1.04/1.22               sk_F)))),
% 1.04/1.22      inference('demod', [status(thm)], ['250', '251', '252'])).
% 1.04/1.22  thf('254', plain,
% 1.04/1.22      (~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.04/1.22      inference('sup-', [status(thm)], ['0', '1'])).
% 1.04/1.22  thf('255', plain,
% 1.04/1.22      (((~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ k1_xboole_0 @ sk_G @ sk_H))
% 1.04/1.22         | ((k1_xboole_0) = (sk_E))))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 1.04/1.22               sk_F)))),
% 1.04/1.22      inference('sup-', [status(thm)], ['253', '254'])).
% 1.04/1.22  thf('256', plain,
% 1.04/1.22      (![X42 : $i, X44 : $i, X46 : $i]:
% 1.04/1.22         ((k4_zfmisc_1 @ X42 @ k1_xboole_0 @ X44 @ X46) = (k1_xboole_0))),
% 1.04/1.22      inference('simplify', [status(thm)], ['125'])).
% 1.04/1.22  thf('257', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.04/1.22      inference('clc', [status(thm)], ['102', '114'])).
% 1.04/1.22  thf('258', plain,
% 1.04/1.22      ((((k1_xboole_0) = (sk_E)))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 1.04/1.22               sk_F)))),
% 1.04/1.22      inference('demod', [status(thm)], ['255', '256', '257'])).
% 1.04/1.22  thf('259', plain,
% 1.04/1.22      (~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.04/1.22      inference('sup-', [status(thm)], ['0', '1'])).
% 1.04/1.22  thf('260', plain,
% 1.04/1.22      ((~ (v1_xboole_0 @ (k4_zfmisc_1 @ k1_xboole_0 @ sk_F @ sk_G @ sk_H)))
% 1.04/1.22         <= (~
% 1.04/1.22             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 1.04/1.22               sk_F)))),
% 1.04/1.22      inference('sup-', [status(thm)], ['258', '259'])).
% 1.04/1.22  thf('261', plain,
% 1.04/1.22      (![X43 : $i, X44 : $i, X46 : $i]:
% 1.04/1.22         ((k4_zfmisc_1 @ k1_xboole_0 @ X43 @ X44 @ X46) = (k1_xboole_0))),
% 1.04/1.22      inference('simplify', [status(thm)], ['17'])).
% 1.04/1.22  thf('262', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.04/1.22      inference('clc', [status(thm)], ['102', '114'])).
% 1.04/1.22  thf('263', plain,
% 1.04/1.22      (((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_F))),
% 1.04/1.22      inference('demod', [status(thm)], ['260', '261', '262'])).
% 1.04/1.22  thf('264', plain,
% 1.04/1.22      (~
% 1.04/1.22       ((r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_E)) | 
% 1.04/1.22       ~
% 1.04/1.22       ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_F)) | 
% 1.04/1.22       ~
% 1.04/1.22       ((r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_G)) | 
% 1.04/1.22       ~
% 1.04/1.22       ((r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_H))),
% 1.04/1.22      inference('split', [status(esa)], ['30'])).
% 1.04/1.22  thf('265', plain,
% 1.04/1.22      (~
% 1.04/1.22       ((r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_E))),
% 1.04/1.22      inference('sat_resolution*', [status(thm)], ['133', '198', '263', '264'])).
% 1.04/1.22  thf('266', plain,
% 1.04/1.22      (~ (r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_E)),
% 1.04/1.22      inference('simpl_trail', [status(thm)], ['31', '265'])).
% 1.04/1.22  thf('267', plain,
% 1.04/1.22      ((~ (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ sk_E)
% 1.04/1.22        | ((sk_A) = (k1_xboole_0))
% 1.04/1.22        | ((sk_B_1) = (k1_xboole_0))
% 1.04/1.22        | ((sk_C) = (k1_xboole_0))
% 1.04/1.22        | ((sk_D) = (k1_xboole_0)))),
% 1.04/1.22      inference('sup-', [status(thm)], ['29', '266'])).
% 1.04/1.22  thf('268', plain,
% 1.04/1.22      ((((sk_H) = (k1_xboole_0))
% 1.04/1.22        | ((sk_G) = (k1_xboole_0))
% 1.04/1.22        | ((sk_F) = (k1_xboole_0))
% 1.04/1.22        | ((sk_E) = (k1_xboole_0))
% 1.04/1.22        | ((sk_D) = (k1_xboole_0))
% 1.04/1.22        | ((sk_C) = (k1_xboole_0))
% 1.04/1.22        | ((sk_B_1) = (k1_xboole_0))
% 1.04/1.22        | ((sk_A) = (k1_xboole_0)))),
% 1.04/1.22      inference('sup-', [status(thm)], ['26', '267'])).
% 1.04/1.22  thf('269', plain, (((k3_xboole_0 @ sk_H @ sk_D) = (sk_H))),
% 1.04/1.22      inference('sup-', [status(thm)], ['60', '61'])).
% 1.04/1.22  thf('270', plain,
% 1.04/1.22      ((((k3_xboole_0 @ sk_H @ k1_xboole_0) = (sk_H))
% 1.04/1.22        | ((sk_A) = (k1_xboole_0))
% 1.04/1.22        | ((sk_B_1) = (k1_xboole_0))
% 1.04/1.22        | ((sk_C) = (k1_xboole_0))
% 1.04/1.22        | ((sk_E) = (k1_xboole_0))
% 1.04/1.22        | ((sk_F) = (k1_xboole_0))
% 1.04/1.22        | ((sk_G) = (k1_xboole_0))
% 1.04/1.22        | ((sk_H) = (k1_xboole_0)))),
% 1.04/1.22      inference('sup+', [status(thm)], ['268', '269'])).
% 1.04/1.22  thf('271', plain,
% 1.04/1.22      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 1.04/1.22      inference('cnf', [status(esa)], [t2_boole])).
% 1.04/1.22  thf('272', plain,
% 1.04/1.22      ((((k1_xboole_0) = (sk_H))
% 1.04/1.22        | ((sk_A) = (k1_xboole_0))
% 1.04/1.22        | ((sk_B_1) = (k1_xboole_0))
% 1.04/1.22        | ((sk_C) = (k1_xboole_0))
% 1.04/1.22        | ((sk_E) = (k1_xboole_0))
% 1.04/1.22        | ((sk_F) = (k1_xboole_0))
% 1.04/1.22        | ((sk_G) = (k1_xboole_0))
% 1.04/1.22        | ((sk_H) = (k1_xboole_0)))),
% 1.04/1.22      inference('demod', [status(thm)], ['270', '271'])).
% 1.04/1.22  thf('273', plain,
% 1.04/1.22      ((((sk_G) = (k1_xboole_0))
% 1.04/1.22        | ((sk_F) = (k1_xboole_0))
% 1.04/1.22        | ((sk_E) = (k1_xboole_0))
% 1.04/1.22        | ((sk_C) = (k1_xboole_0))
% 1.04/1.22        | ((sk_B_1) = (k1_xboole_0))
% 1.04/1.22        | ((sk_A) = (k1_xboole_0))
% 1.04/1.22        | ((k1_xboole_0) = (sk_H)))),
% 1.04/1.22      inference('simplify', [status(thm)], ['272'])).
% 1.04/1.22  thf('274', plain, (((k3_xboole_0 @ sk_G @ sk_C) = (sk_G))),
% 1.04/1.22      inference('sup-', [status(thm)], ['69', '70'])).
% 1.04/1.22  thf('275', plain,
% 1.04/1.22      ((((k3_xboole_0 @ sk_G @ k1_xboole_0) = (sk_G))
% 1.04/1.22        | ((k1_xboole_0) = (sk_H))
% 1.04/1.22        | ((sk_A) = (k1_xboole_0))
% 1.04/1.22        | ((sk_B_1) = (k1_xboole_0))
% 1.04/1.22        | ((sk_E) = (k1_xboole_0))
% 1.04/1.22        | ((sk_F) = (k1_xboole_0))
% 1.04/1.22        | ((sk_G) = (k1_xboole_0)))),
% 1.04/1.22      inference('sup+', [status(thm)], ['273', '274'])).
% 1.04/1.22  thf('276', plain,
% 1.04/1.22      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 1.04/1.22      inference('cnf', [status(esa)], [t2_boole])).
% 1.04/1.22  thf('277', plain,
% 1.04/1.22      ((((k1_xboole_0) = (sk_G))
% 1.04/1.22        | ((k1_xboole_0) = (sk_H))
% 1.04/1.22        | ((sk_A) = (k1_xboole_0))
% 1.04/1.22        | ((sk_B_1) = (k1_xboole_0))
% 1.04/1.22        | ((sk_E) = (k1_xboole_0))
% 1.04/1.22        | ((sk_F) = (k1_xboole_0))
% 1.04/1.22        | ((sk_G) = (k1_xboole_0)))),
% 1.04/1.22      inference('demod', [status(thm)], ['275', '276'])).
% 1.04/1.22  thf('278', plain,
% 1.04/1.22      ((((sk_F) = (k1_xboole_0))
% 1.04/1.22        | ((sk_E) = (k1_xboole_0))
% 1.04/1.22        | ((sk_B_1) = (k1_xboole_0))
% 1.04/1.22        | ((sk_A) = (k1_xboole_0))
% 1.04/1.22        | ((k1_xboole_0) = (sk_H))
% 1.04/1.22        | ((k1_xboole_0) = (sk_G)))),
% 1.04/1.22      inference('simplify', [status(thm)], ['277'])).
% 1.04/1.22  thf('279', plain, (((k3_xboole_0 @ sk_F @ sk_B_1) = (sk_F))),
% 1.04/1.22      inference('sup-', [status(thm)], ['78', '79'])).
% 1.04/1.22  thf('280', plain,
% 1.04/1.22      ((((k3_xboole_0 @ sk_F @ k1_xboole_0) = (sk_F))
% 1.04/1.22        | ((k1_xboole_0) = (sk_G))
% 1.04/1.22        | ((k1_xboole_0) = (sk_H))
% 1.04/1.22        | ((sk_A) = (k1_xboole_0))
% 1.04/1.22        | ((sk_E) = (k1_xboole_0))
% 1.04/1.22        | ((sk_F) = (k1_xboole_0)))),
% 1.04/1.22      inference('sup+', [status(thm)], ['278', '279'])).
% 1.04/1.22  thf('281', plain,
% 1.04/1.22      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 1.04/1.22      inference('cnf', [status(esa)], [t2_boole])).
% 1.04/1.22  thf('282', plain,
% 1.04/1.22      ((((k1_xboole_0) = (sk_F))
% 1.04/1.22        | ((k1_xboole_0) = (sk_G))
% 1.04/1.22        | ((k1_xboole_0) = (sk_H))
% 1.04/1.22        | ((sk_A) = (k1_xboole_0))
% 1.04/1.22        | ((sk_E) = (k1_xboole_0))
% 1.04/1.22        | ((sk_F) = (k1_xboole_0)))),
% 1.04/1.22      inference('demod', [status(thm)], ['280', '281'])).
% 1.04/1.22  thf('283', plain,
% 1.04/1.22      ((((sk_E) = (k1_xboole_0))
% 1.04/1.22        | ((sk_A) = (k1_xboole_0))
% 1.04/1.22        | ((k1_xboole_0) = (sk_H))
% 1.04/1.22        | ((k1_xboole_0) = (sk_G))
% 1.04/1.22        | ((k1_xboole_0) = (sk_F)))),
% 1.04/1.22      inference('simplify', [status(thm)], ['282'])).
% 1.04/1.22  thf('284', plain, (((k3_xboole_0 @ sk_E @ sk_A) = (sk_E))),
% 1.04/1.22      inference('sup-', [status(thm)], ['87', '88'])).
% 1.04/1.22  thf('285', plain,
% 1.04/1.22      ((((k3_xboole_0 @ sk_E @ k1_xboole_0) = (sk_E))
% 1.04/1.22        | ((k1_xboole_0) = (sk_F))
% 1.04/1.22        | ((k1_xboole_0) = (sk_G))
% 1.04/1.22        | ((k1_xboole_0) = (sk_H))
% 1.04/1.22        | ((sk_E) = (k1_xboole_0)))),
% 1.04/1.22      inference('sup+', [status(thm)], ['283', '284'])).
% 1.04/1.22  thf('286', plain,
% 1.04/1.22      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 1.04/1.22      inference('cnf', [status(esa)], [t2_boole])).
% 1.04/1.22  thf('287', plain,
% 1.04/1.22      ((((k1_xboole_0) = (sk_E))
% 1.04/1.22        | ((k1_xboole_0) = (sk_F))
% 1.04/1.22        | ((k1_xboole_0) = (sk_G))
% 1.04/1.22        | ((k1_xboole_0) = (sk_H))
% 1.04/1.22        | ((sk_E) = (k1_xboole_0)))),
% 1.04/1.22      inference('demod', [status(thm)], ['285', '286'])).
% 1.04/1.22  thf('288', plain,
% 1.04/1.22      ((((k1_xboole_0) = (sk_H))
% 1.04/1.22        | ((k1_xboole_0) = (sk_G))
% 1.04/1.22        | ((k1_xboole_0) = (sk_F))
% 1.04/1.22        | ((k1_xboole_0) = (sk_E)))),
% 1.04/1.22      inference('simplify', [status(thm)], ['287'])).
% 1.04/1.22  thf('289', plain,
% 1.04/1.22      (~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.04/1.22      inference('sup-', [status(thm)], ['0', '1'])).
% 1.04/1.22  thf('290', plain,
% 1.04/1.22      ((~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ k1_xboole_0))
% 1.04/1.22        | ((k1_xboole_0) = (sk_E))
% 1.04/1.22        | ((k1_xboole_0) = (sk_F))
% 1.04/1.22        | ((k1_xboole_0) = (sk_G)))),
% 1.04/1.22      inference('sup-', [status(thm)], ['288', '289'])).
% 1.04/1.22  thf('291', plain,
% 1.04/1.22      (![X42 : $i, X43 : $i, X44 : $i]:
% 1.04/1.22         ((k4_zfmisc_1 @ X42 @ X43 @ X44 @ k1_xboole_0) = (k1_xboole_0))),
% 1.04/1.22      inference('simplify', [status(thm)], ['42'])).
% 1.04/1.22  thf('292', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.04/1.22      inference('clc', [status(thm)], ['102', '114'])).
% 1.04/1.22  thf('293', plain,
% 1.04/1.22      ((((k1_xboole_0) = (sk_E))
% 1.04/1.22        | ((k1_xboole_0) = (sk_F))
% 1.04/1.22        | ((k1_xboole_0) = (sk_G)))),
% 1.04/1.22      inference('demod', [status(thm)], ['290', '291', '292'])).
% 1.04/1.22  thf('294', plain,
% 1.04/1.22      (~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.04/1.22      inference('sup-', [status(thm)], ['0', '1'])).
% 1.04/1.22  thf('295', plain,
% 1.04/1.22      ((~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ sk_F @ k1_xboole_0 @ sk_H))
% 1.04/1.22        | ((k1_xboole_0) = (sk_F))
% 1.04/1.22        | ((k1_xboole_0) = (sk_E)))),
% 1.04/1.22      inference('sup-', [status(thm)], ['293', '294'])).
% 1.04/1.22  thf('296', plain,
% 1.04/1.22      (![X42 : $i, X43 : $i, X46 : $i]:
% 1.04/1.22         ((k4_zfmisc_1 @ X42 @ X43 @ k1_xboole_0 @ X46) = (k1_xboole_0))),
% 1.04/1.22      inference('simplify', [status(thm)], ['119'])).
% 1.04/1.22  thf('297', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.04/1.22      inference('clc', [status(thm)], ['102', '114'])).
% 1.04/1.22  thf('298', plain, ((((k1_xboole_0) = (sk_F)) | ((k1_xboole_0) = (sk_E)))),
% 1.04/1.22      inference('demod', [status(thm)], ['295', '296', '297'])).
% 1.04/1.22  thf('299', plain,
% 1.04/1.22      (~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 1.04/1.22      inference('sup-', [status(thm)], ['0', '1'])).
% 1.04/1.22  thf('300', plain,
% 1.04/1.22      ((~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ k1_xboole_0 @ sk_G @ sk_H))
% 1.04/1.22        | ((k1_xboole_0) = (sk_E)))),
% 1.04/1.22      inference('sup-', [status(thm)], ['298', '299'])).
% 1.04/1.22  thf('301', plain,
% 1.04/1.22      (![X42 : $i, X44 : $i, X46 : $i]:
% 1.04/1.22         ((k4_zfmisc_1 @ X42 @ k1_xboole_0 @ X44 @ X46) = (k1_xboole_0))),
% 1.04/1.22      inference('simplify', [status(thm)], ['125'])).
% 1.04/1.22  thf('302', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.04/1.22      inference('clc', [status(thm)], ['102', '114'])).
% 1.04/1.22  thf('303', plain, (((k1_xboole_0) = (sk_E))),
% 1.04/1.22      inference('demod', [status(thm)], ['300', '301', '302'])).
% 1.04/1.22  thf('304', plain,
% 1.04/1.22      (![X43 : $i, X44 : $i, X46 : $i]:
% 1.04/1.22         ((k4_zfmisc_1 @ k1_xboole_0 @ X43 @ X44 @ X46) = (k1_xboole_0))),
% 1.04/1.22      inference('simplify', [status(thm)], ['17'])).
% 1.04/1.22  thf('305', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.04/1.22      inference('clc', [status(thm)], ['102', '114'])).
% 1.04/1.22  thf('306', plain, ($false),
% 1.04/1.22      inference('demod', [status(thm)], ['2', '303', '304', '305'])).
% 1.04/1.22  
% 1.04/1.22  % SZS output end Refutation
% 1.04/1.22  
% 1.04/1.23  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
