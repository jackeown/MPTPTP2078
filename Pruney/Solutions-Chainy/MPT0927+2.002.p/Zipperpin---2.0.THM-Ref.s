%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Qx0nfuhdKO

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:19 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  251 ( 828 expanded)
%              Number of leaves         :   36 ( 272 expanded)
%              Depth                    :   30
%              Number of atoms          : 2090 (11690 expanded)
%              Number of equality atoms :  142 ( 257 expanded)
%              Maximal formula depth    :   27 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k10_mcart_1_type,type,(
    k10_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_I_type,type,(
    sk_I: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k8_mcart_1_type,type,(
    k8_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k11_mcart_1_type,type,(
    k11_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_mcart_1_type,type,(
    k9_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

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

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k4_zfmisc_1 @ X18 @ X19 @ X20 @ X21 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X18 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X22 ) @ X23 )
      | ~ ( r2_hidden @ X22 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X4 ) @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_I ) @ ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_zfmisc_1 @ X15 @ X16 @ X17 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('6',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X22 ) @ X23 )
      | ~ ( r2_hidden @ X22 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) @ ( k2_zfmisc_1 @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X22 ) @ X23 )
      | ~ ( r2_hidden @ X22 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('10',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_E ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ X14 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('13',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_E @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('14',plain,(
    ! [X12: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('15',plain,(
    r2_hidden @ sk_E @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['13','14'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('16',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r1_tarski @ X10 @ X8 )
      | ( X9
       != ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('17',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_tarski @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    r1_tarski @ sk_E @ sk_A ),
    inference('sup-',[status(thm)],['15','17'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_A ),
    inference('sup-',[status(thm)],['10','20'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('23',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('25',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ( ( k8_mcart_1 @ X25 @ X26 @ X27 @ X29 @ X28 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ X28 ) ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k4_zfmisc_1 @ X25 @ X26 @ X27 @ X29 ) )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('26',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) )
    | ( sk_C_2 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_E )
    | ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_F )
    | ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_G )
    | ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_E )
   <= ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_E ) ),
    inference(split,[status(esa)],['27'])).

thf('29',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X25 @ X26 @ X27 @ X29 @ X28 )
        = ( k2_mcart_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k4_zfmisc_1 @ X25 @ X26 @ X27 @ X29 ) )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('31',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I )
      = ( k2_mcart_1 @ sk_I ) )
    | ( sk_C_2 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_H )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_H ) ),
    inference(split,[status(esa)],['27'])).

thf('33',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_I ) @ sk_H )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_2 = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r2_hidden @ sk_I @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k4_zfmisc_1 @ X18 @ X19 @ X20 @ X21 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X18 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('36',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X22 ) @ X24 )
      | ~ ( r2_hidden @ X22 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X4 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_I ) @ sk_H ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_2 = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_H ) ),
    inference(demod,[status(thm)],['33','38'])).

thf('40',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_I ) @ sk_H ),
    inference('sup-',[status(thm)],['34','37'])).

thf('41',plain,(
    m1_subset_1 @ sk_H @ ( k1_zfmisc_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ X14 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_D ) )
    | ( r2_hidden @ sk_H @ ( k1_zfmisc_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X12: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('45',plain,(
    r2_hidden @ sk_H @ ( k1_zfmisc_1 @ sk_D ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_tarski @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('47',plain,(
    r1_tarski @ sk_H @ sk_D ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_D )
      | ~ ( r2_hidden @ X0 @ sk_H ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_I ) @ sk_D ),
    inference('sup-',[status(thm)],['40','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('52',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_C_2 = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['39','52'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('54',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('55',plain,
    ( ( ( sk_C_2 = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_H ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('57',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ X14 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('59',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_C_2 ) )
    | ( r2_hidden @ sk_G @ ( k1_zfmisc_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X12: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('61',plain,(
    r2_hidden @ sk_G @ ( k1_zfmisc_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_tarski @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('63',plain,(
    r1_tarski @ sk_G @ sk_C_2 ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_2 )
      | ~ ( r2_hidden @ X0 @ sk_G ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( v1_xboole_0 @ sk_G )
    | ( r2_hidden @ ( sk_B @ sk_G ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['56','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('68',plain,
    ( ( v1_xboole_0 @ sk_G )
    | ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_G ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['55','68'])).

thf('70',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('71',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_G ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_H ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_zfmisc_1 @ X15 @ X16 @ X17 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('73',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('74',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X22 ) @ X24 )
      | ~ ( r2_hidden @ X22 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['72','77'])).

thf('79',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k4_zfmisc_1 @ X18 @ X19 @ X20 @ X21 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X18 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('80',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('81',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X22 ) @ X23 )
      | ~ ( r2_hidden @ X22 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['79','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ) ),
    inference('sup-',[status(thm)],['78','85'])).

thf('87',plain,(
    r2_hidden @ sk_I @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('89',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ~ ( v1_xboole_0 @ sk_G ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['71','90'])).

thf('92',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('93',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ X14 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('95',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_B_1 ) )
    | ( r2_hidden @ sk_F @ ( k1_zfmisc_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X12: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('97',plain,(
    r2_hidden @ sk_F @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_tarski @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('99',plain,(
    r1_tarski @ sk_F @ sk_B_1 ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( v1_xboole_0 @ sk_F )
    | ( r2_hidden @ ( sk_B @ sk_F ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['92','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('104',plain,
    ( ( v1_xboole_0 @ sk_F )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['91','104'])).

thf('106',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('107',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_H ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('109',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_zfmisc_1 @ X15 @ X16 @ X17 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ X1 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['108','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['79','84'])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('116',plain,(
    ~ ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['107','116'])).

thf('118',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('120',plain,
    ( ( v1_xboole_0 @ sk_E )
    | ( r2_hidden @ ( sk_B @ sk_E ) @ sk_A ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('122',plain,
    ( ( v1_xboole_0 @ sk_E )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['117','122'])).

thf('124',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('125',plain,
    ( ( v1_xboole_0 @ sk_E )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_H ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('127',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('128',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ X1 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['79','84'])).

thf('130',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( v1_xboole_0 @ ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('132',plain,(
    ~ ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_H ),
    inference('sup-',[status(thm)],['125','132'])).

thf('134',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ( ( k10_mcart_1 @ X25 @ X26 @ X27 @ X29 @ X28 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k4_zfmisc_1 @ X25 @ X26 @ X27 @ X29 ) )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('136',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) )
    | ( sk_C_2 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,
    ( ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_G )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_G ) ),
    inference(split,[status(esa)],['27'])).

thf('138',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) @ sk_G )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_2 = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_I ) @ ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('140',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_zfmisc_1 @ X15 @ X16 @ X17 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('141',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X22 ) @ X24 )
      | ~ ( r2_hidden @ X22 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('142',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) @ sk_G ),
    inference('sup-',[status(thm)],['139','142'])).

thf('144',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_2 = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_G ) ),
    inference(demod,[status(thm)],['138','143'])).

thf('145',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('146',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_C_2 = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('148',plain,
    ( ( ( sk_C_2 = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_G ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) @ sk_G ),
    inference('sup-',[status(thm)],['139','142'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_2 )
      | ~ ( r2_hidden @ X0 @ sk_G ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('151',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) @ sk_C_2 ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('153',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['148','153'])).

thf('155',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('156',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_G ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) @ ( k2_zfmisc_1 @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('158',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X22 ) @ X24 )
      | ~ ( r2_hidden @ X22 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('159',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_F ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('161',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('163',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['156','163'])).

thf('165',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('166',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_G ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('168',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('170',plain,(
    r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_G ),
    inference(demod,[status(thm)],['168','169'])).

thf('171',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ( ( k9_mcart_1 @ X25 @ X26 @ X27 @ X29 @ X28 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ X28 ) ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k4_zfmisc_1 @ X25 @ X26 @ X27 @ X29 ) )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('173',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) )
    | ( sk_C_2 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,
    ( ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_F )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_F ) ),
    inference(split,[status(esa)],['27'])).

thf('175',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_F )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_2 = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_F ),
    inference('sup-',[status(thm)],['157','158'])).

thf('177',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_2 = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_F ) ),
    inference(demod,[status(thm)],['175','176'])).

thf('178',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('179',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_C_2 = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('181',plain,
    ( ( ( sk_C_2 = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_F ) ),
    inference(demod,[status(thm)],['179','180'])).

thf('182',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('183',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('185',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_F ) ),
    inference(demod,[status(thm)],['183','184'])).

thf('186',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('187',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('189',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_F ) ),
    inference(demod,[status(thm)],['187','188'])).

thf('190',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('191',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('193',plain,(
    r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_F ),
    inference(demod,[status(thm)],['191','192'])).

thf('194',plain,
    ( ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_E )
    | ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_F )
    | ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_G )
    | ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_H ) ),
    inference(split,[status(esa)],['27'])).

thf('195',plain,(
    ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['133','170','193','194'])).

thf('196',plain,(
    ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I ) @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['28','195'])).

thf('197',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_E )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','196'])).

thf('198',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_E ),
    inference('sup-',[status(thm)],['8','9'])).

thf('199',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['197','198'])).

thf('200',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('201',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('203',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('204',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('205',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('207',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['205','206'])).

thf('208',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('209',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['207','208'])).

thf('210',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('211',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['209','210'])).

thf('212',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('213',plain,(
    $false ),
    inference(demod,[status(thm)],['23','211','212'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Qx0nfuhdKO
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:42:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.69  % Solved by: fo/fo7.sh
% 0.46/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.69  % done 401 iterations in 0.222s
% 0.46/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.69  % SZS output start Refutation
% 0.46/0.69  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.69  thf(sk_D_type, type, sk_D: $i).
% 0.46/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.69  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.69  thf(k10_mcart_1_type, type, k10_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.46/0.69  thf(sk_F_type, type, sk_F: $i).
% 0.46/0.69  thf(sk_E_type, type, sk_E: $i).
% 0.46/0.69  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.46/0.69  thf(sk_B_type, type, sk_B: $i > $i).
% 0.46/0.69  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.46/0.69  thf(sk_I_type, type, sk_I: $i).
% 0.46/0.69  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.46/0.69  thf(k8_mcart_1_type, type, k8_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.46/0.69  thf(k11_mcart_1_type, type, k11_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.46/0.69  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.69  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.46/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.69  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.46/0.69  thf(sk_H_type, type, sk_H: $i).
% 0.46/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.69  thf(k9_mcart_1_type, type, k9_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.46/0.69  thf(sk_G_type, type, sk_G: $i).
% 0.46/0.69  thf(t87_mcart_1, conjecture,
% 0.46/0.69    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.46/0.69     ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.69       ( ![F:$i]:
% 0.46/0.69         ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ B ) ) =>
% 0.46/0.69           ( ![G:$i]:
% 0.46/0.69             ( ( m1_subset_1 @ G @ ( k1_zfmisc_1 @ C ) ) =>
% 0.46/0.69               ( ![H:$i]:
% 0.46/0.69                 ( ( m1_subset_1 @ H @ ( k1_zfmisc_1 @ D ) ) =>
% 0.46/0.69                   ( ![I:$i]:
% 0.46/0.69                     ( ( m1_subset_1 @ I @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.46/0.69                       ( ( r2_hidden @ I @ ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 0.46/0.69                         ( ( r2_hidden @ ( k8_mcart_1 @ A @ B @ C @ D @ I ) @ E ) & 
% 0.46/0.69                           ( r2_hidden @ ( k9_mcart_1 @ A @ B @ C @ D @ I ) @ F ) & 
% 0.46/0.69                           ( r2_hidden @
% 0.46/0.69                             ( k10_mcart_1 @ A @ B @ C @ D @ I ) @ G ) & 
% 0.46/0.69                           ( r2_hidden @
% 0.46/0.69                             ( k11_mcart_1 @ A @ B @ C @ D @ I ) @ H ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.69    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.46/0.69        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.69          ( ![F:$i]:
% 0.46/0.69            ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ B ) ) =>
% 0.46/0.69              ( ![G:$i]:
% 0.46/0.69                ( ( m1_subset_1 @ G @ ( k1_zfmisc_1 @ C ) ) =>
% 0.46/0.69                  ( ![H:$i]:
% 0.46/0.69                    ( ( m1_subset_1 @ H @ ( k1_zfmisc_1 @ D ) ) =>
% 0.46/0.69                      ( ![I:$i]:
% 0.46/0.69                        ( ( m1_subset_1 @ I @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.46/0.69                          ( ( r2_hidden @ I @ ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 0.46/0.69                            ( ( r2_hidden @
% 0.46/0.69                                ( k8_mcart_1 @ A @ B @ C @ D @ I ) @ E ) & 
% 0.46/0.69                              ( r2_hidden @
% 0.46/0.69                                ( k9_mcart_1 @ A @ B @ C @ D @ I ) @ F ) & 
% 0.46/0.69                              ( r2_hidden @
% 0.46/0.69                                ( k10_mcart_1 @ A @ B @ C @ D @ I ) @ G ) & 
% 0.46/0.69                              ( r2_hidden @
% 0.46/0.69                                ( k11_mcart_1 @ A @ B @ C @ D @ I ) @ H ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.46/0.69    inference('cnf.neg', [status(esa)], [t87_mcart_1])).
% 0.46/0.69  thf('0', plain,
% 0.46/0.69      ((r2_hidden @ sk_I @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf(d4_zfmisc_1, axiom,
% 0.46/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.69     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.46/0.69       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.46/0.69  thf('1', plain,
% 0.46/0.69      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.69         ((k4_zfmisc_1 @ X18 @ X19 @ X20 @ X21)
% 0.46/0.69           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X18 @ X19 @ X20) @ X21))),
% 0.46/0.69      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.46/0.69  thf(t10_mcart_1, axiom,
% 0.46/0.69    (![A:$i,B:$i,C:$i]:
% 0.46/0.69     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.46/0.69       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.46/0.69         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.46/0.69  thf('2', plain,
% 0.46/0.69      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.46/0.69         ((r2_hidden @ (k1_mcart_1 @ X22) @ X23)
% 0.46/0.69          | ~ (r2_hidden @ X22 @ (k2_zfmisc_1 @ X23 @ X24)))),
% 0.46/0.69      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.46/0.69  thf('3', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.69         (~ (r2_hidden @ X4 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.46/0.69          | (r2_hidden @ (k1_mcart_1 @ X4) @ (k3_zfmisc_1 @ X3 @ X2 @ X1)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.69  thf('4', plain,
% 0.46/0.69      ((r2_hidden @ (k1_mcart_1 @ sk_I) @ (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G))),
% 0.46/0.69      inference('sup-', [status(thm)], ['0', '3'])).
% 0.46/0.69  thf(d3_zfmisc_1, axiom,
% 0.46/0.69    (![A:$i,B:$i,C:$i]:
% 0.46/0.69     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.46/0.69       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.46/0.69  thf('5', plain,
% 0.46/0.69      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.69         ((k3_zfmisc_1 @ X15 @ X16 @ X17)
% 0.46/0.69           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16) @ X17))),
% 0.46/0.69      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.46/0.69  thf('6', plain,
% 0.46/0.69      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.46/0.69         ((r2_hidden @ (k1_mcart_1 @ X22) @ X23)
% 0.46/0.69          | ~ (r2_hidden @ X22 @ (k2_zfmisc_1 @ X23 @ X24)))),
% 0.46/0.69      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.46/0.69  thf('7', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.69         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.46/0.69          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['5', '6'])).
% 0.46/0.69  thf('8', plain,
% 0.46/0.69      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I)) @ 
% 0.46/0.69        (k2_zfmisc_1 @ sk_E @ sk_F))),
% 0.46/0.69      inference('sup-', [status(thm)], ['4', '7'])).
% 0.46/0.69  thf('9', plain,
% 0.46/0.69      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.46/0.69         ((r2_hidden @ (k1_mcart_1 @ X22) @ X23)
% 0.46/0.69          | ~ (r2_hidden @ X22 @ (k2_zfmisc_1 @ X23 @ X24)))),
% 0.46/0.69      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.46/0.69  thf('10', plain,
% 0.46/0.69      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ sk_E)),
% 0.46/0.69      inference('sup-', [status(thm)], ['8', '9'])).
% 0.46/0.69  thf('11', plain, ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf(t2_subset, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( m1_subset_1 @ A @ B ) =>
% 0.46/0.69       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.46/0.69  thf('12', plain,
% 0.46/0.69      (![X13 : $i, X14 : $i]:
% 0.46/0.69         ((r2_hidden @ X13 @ X14)
% 0.46/0.69          | (v1_xboole_0 @ X14)
% 0.46/0.69          | ~ (m1_subset_1 @ X13 @ X14))),
% 0.46/0.69      inference('cnf', [status(esa)], [t2_subset])).
% 0.46/0.69  thf('13', plain,
% 0.46/0.69      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.46/0.69        | (r2_hidden @ sk_E @ (k1_zfmisc_1 @ sk_A)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['11', '12'])).
% 0.46/0.69  thf(fc1_subset_1, axiom,
% 0.46/0.69    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.46/0.69  thf('14', plain, (![X12 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.46/0.69      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.46/0.69  thf('15', plain, ((r2_hidden @ sk_E @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.69      inference('clc', [status(thm)], ['13', '14'])).
% 0.46/0.69  thf(d1_zfmisc_1, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.46/0.69       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.46/0.69  thf('16', plain,
% 0.46/0.69      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.46/0.69         (~ (r2_hidden @ X10 @ X9)
% 0.46/0.69          | (r1_tarski @ X10 @ X8)
% 0.46/0.69          | ((X9) != (k1_zfmisc_1 @ X8)))),
% 0.46/0.69      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.46/0.69  thf('17', plain,
% 0.46/0.69      (![X8 : $i, X10 : $i]:
% 0.46/0.69         ((r1_tarski @ X10 @ X8) | ~ (r2_hidden @ X10 @ (k1_zfmisc_1 @ X8)))),
% 0.46/0.69      inference('simplify', [status(thm)], ['16'])).
% 0.46/0.69  thf('18', plain, ((r1_tarski @ sk_E @ sk_A)),
% 0.46/0.69      inference('sup-', [status(thm)], ['15', '17'])).
% 0.46/0.69  thf(d3_tarski, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( r1_tarski @ A @ B ) <=>
% 0.46/0.69       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.46/0.69  thf('19', plain,
% 0.46/0.69      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.46/0.69         (~ (r2_hidden @ X3 @ X4)
% 0.46/0.69          | (r2_hidden @ X3 @ X5)
% 0.46/0.69          | ~ (r1_tarski @ X4 @ X5))),
% 0.46/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.69  thf('20', plain,
% 0.46/0.69      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_E))),
% 0.46/0.69      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.69  thf('21', plain,
% 0.46/0.69      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ sk_A)),
% 0.46/0.69      inference('sup-', [status(thm)], ['10', '20'])).
% 0.46/0.69  thf(d1_xboole_0, axiom,
% 0.46/0.69    (![A:$i]:
% 0.46/0.69     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.46/0.69  thf('22', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.46/0.69      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.69  thf('23', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.46/0.69      inference('sup-', [status(thm)], ['21', '22'])).
% 0.46/0.69  thf('24', plain,
% 0.46/0.69      ((m1_subset_1 @ sk_I @ (k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf(t61_mcart_1, axiom,
% 0.46/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.69     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.46/0.69          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.46/0.69          ( ~( ![E:$i]:
% 0.46/0.69               ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.46/0.69                 ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.46/0.69                     ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.46/0.69                   ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.46/0.69                     ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.46/0.69                   ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.46/0.69                     ( k2_mcart_1 @ ( k1_mcart_1 @ E ) ) ) & 
% 0.46/0.69                   ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( k2_mcart_1 @ E ) ) ) ) ) ) ) ))).
% 0.46/0.69  thf('25', plain,
% 0.46/0.69      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.46/0.69         (((X25) = (k1_xboole_0))
% 0.46/0.69          | ((X26) = (k1_xboole_0))
% 0.46/0.69          | ((X27) = (k1_xboole_0))
% 0.46/0.69          | ((k8_mcart_1 @ X25 @ X26 @ X27 @ X29 @ X28)
% 0.46/0.69              = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ X28))))
% 0.46/0.69          | ~ (m1_subset_1 @ X28 @ (k4_zfmisc_1 @ X25 @ X26 @ X27 @ X29))
% 0.46/0.69          | ((X29) = (k1_xboole_0)))),
% 0.46/0.69      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.46/0.69  thf('26', plain,
% 0.46/0.69      ((((sk_D) = (k1_xboole_0))
% 0.46/0.69        | ((k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I)
% 0.46/0.69            = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))))
% 0.46/0.69        | ((sk_C_2) = (k1_xboole_0))
% 0.46/0.69        | ((sk_B_1) = (k1_xboole_0))
% 0.46/0.69        | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['24', '25'])).
% 0.46/0.69  thf('27', plain,
% 0.46/0.69      ((~ (r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ 
% 0.46/0.69           sk_E)
% 0.46/0.69        | ~ (r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ 
% 0.46/0.69             sk_F)
% 0.46/0.69        | ~ (r2_hidden @ 
% 0.46/0.69             (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ sk_G)
% 0.46/0.69        | ~ (r2_hidden @ 
% 0.46/0.69             (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ sk_H))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('28', plain,
% 0.46/0.69      ((~ (r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ 
% 0.46/0.69           sk_E))
% 0.46/0.69         <= (~
% 0.46/0.69             ((r2_hidden @ 
% 0.46/0.69               (k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ sk_E)))),
% 0.46/0.69      inference('split', [status(esa)], ['27'])).
% 0.46/0.69  thf('29', plain,
% 0.46/0.69      ((m1_subset_1 @ sk_I @ (k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('30', plain,
% 0.46/0.69      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.46/0.69         (((X25) = (k1_xboole_0))
% 0.46/0.69          | ((X26) = (k1_xboole_0))
% 0.46/0.69          | ((X27) = (k1_xboole_0))
% 0.46/0.69          | ((k11_mcart_1 @ X25 @ X26 @ X27 @ X29 @ X28) = (k2_mcart_1 @ X28))
% 0.46/0.69          | ~ (m1_subset_1 @ X28 @ (k4_zfmisc_1 @ X25 @ X26 @ X27 @ X29))
% 0.46/0.69          | ((X29) = (k1_xboole_0)))),
% 0.46/0.69      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.46/0.69  thf('31', plain,
% 0.46/0.69      ((((sk_D) = (k1_xboole_0))
% 0.46/0.69        | ((k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I)
% 0.46/0.69            = (k2_mcart_1 @ sk_I))
% 0.46/0.69        | ((sk_C_2) = (k1_xboole_0))
% 0.46/0.69        | ((sk_B_1) = (k1_xboole_0))
% 0.46/0.69        | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['29', '30'])).
% 0.46/0.69  thf('32', plain,
% 0.46/0.69      ((~ (r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ 
% 0.46/0.69           sk_H))
% 0.46/0.69         <= (~
% 0.46/0.69             ((r2_hidden @ 
% 0.46/0.69               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ sk_H)))),
% 0.46/0.69      inference('split', [status(esa)], ['27'])).
% 0.46/0.69  thf('33', plain,
% 0.46/0.69      (((~ (r2_hidden @ (k2_mcart_1 @ sk_I) @ sk_H)
% 0.46/0.69         | ((sk_A) = (k1_xboole_0))
% 0.46/0.69         | ((sk_B_1) = (k1_xboole_0))
% 0.46/0.69         | ((sk_C_2) = (k1_xboole_0))
% 0.46/0.69         | ((sk_D) = (k1_xboole_0))))
% 0.46/0.69         <= (~
% 0.46/0.69             ((r2_hidden @ 
% 0.46/0.69               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ sk_H)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['31', '32'])).
% 0.46/0.69  thf('34', plain,
% 0.46/0.69      ((r2_hidden @ sk_I @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('35', plain,
% 0.46/0.69      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.69         ((k4_zfmisc_1 @ X18 @ X19 @ X20 @ X21)
% 0.46/0.69           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X18 @ X19 @ X20) @ X21))),
% 0.46/0.69      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.46/0.69  thf('36', plain,
% 0.46/0.69      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.46/0.69         ((r2_hidden @ (k2_mcart_1 @ X22) @ X24)
% 0.46/0.69          | ~ (r2_hidden @ X22 @ (k2_zfmisc_1 @ X23 @ X24)))),
% 0.46/0.69      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.46/0.69  thf('37', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.69         (~ (r2_hidden @ X4 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.46/0.69          | (r2_hidden @ (k2_mcart_1 @ X4) @ X0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['35', '36'])).
% 0.46/0.69  thf('38', plain, ((r2_hidden @ (k2_mcart_1 @ sk_I) @ sk_H)),
% 0.46/0.69      inference('sup-', [status(thm)], ['34', '37'])).
% 0.46/0.69  thf('39', plain,
% 0.46/0.69      (((((sk_A) = (k1_xboole_0))
% 0.46/0.69         | ((sk_B_1) = (k1_xboole_0))
% 0.46/0.69         | ((sk_C_2) = (k1_xboole_0))
% 0.46/0.69         | ((sk_D) = (k1_xboole_0))))
% 0.46/0.69         <= (~
% 0.46/0.69             ((r2_hidden @ 
% 0.46/0.69               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ sk_H)))),
% 0.46/0.69      inference('demod', [status(thm)], ['33', '38'])).
% 0.46/0.69  thf('40', plain, ((r2_hidden @ (k2_mcart_1 @ sk_I) @ sk_H)),
% 0.46/0.69      inference('sup-', [status(thm)], ['34', '37'])).
% 0.46/0.69  thf('41', plain, ((m1_subset_1 @ sk_H @ (k1_zfmisc_1 @ sk_D))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('42', plain,
% 0.46/0.69      (![X13 : $i, X14 : $i]:
% 0.46/0.69         ((r2_hidden @ X13 @ X14)
% 0.46/0.69          | (v1_xboole_0 @ X14)
% 0.46/0.69          | ~ (m1_subset_1 @ X13 @ X14))),
% 0.46/0.69      inference('cnf', [status(esa)], [t2_subset])).
% 0.46/0.69  thf('43', plain,
% 0.46/0.69      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_D))
% 0.46/0.69        | (r2_hidden @ sk_H @ (k1_zfmisc_1 @ sk_D)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['41', '42'])).
% 0.46/0.69  thf('44', plain, (![X12 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.46/0.69      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.46/0.69  thf('45', plain, ((r2_hidden @ sk_H @ (k1_zfmisc_1 @ sk_D))),
% 0.46/0.69      inference('clc', [status(thm)], ['43', '44'])).
% 0.46/0.69  thf('46', plain,
% 0.46/0.69      (![X8 : $i, X10 : $i]:
% 0.46/0.69         ((r1_tarski @ X10 @ X8) | ~ (r2_hidden @ X10 @ (k1_zfmisc_1 @ X8)))),
% 0.46/0.69      inference('simplify', [status(thm)], ['16'])).
% 0.46/0.69  thf('47', plain, ((r1_tarski @ sk_H @ sk_D)),
% 0.46/0.69      inference('sup-', [status(thm)], ['45', '46'])).
% 0.46/0.69  thf('48', plain,
% 0.46/0.69      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.46/0.69         (~ (r2_hidden @ X3 @ X4)
% 0.46/0.69          | (r2_hidden @ X3 @ X5)
% 0.46/0.69          | ~ (r1_tarski @ X4 @ X5))),
% 0.46/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.69  thf('49', plain,
% 0.46/0.69      (![X0 : $i]: ((r2_hidden @ X0 @ sk_D) | ~ (r2_hidden @ X0 @ sk_H))),
% 0.46/0.69      inference('sup-', [status(thm)], ['47', '48'])).
% 0.46/0.69  thf('50', plain, ((r2_hidden @ (k2_mcart_1 @ sk_I) @ sk_D)),
% 0.46/0.69      inference('sup-', [status(thm)], ['40', '49'])).
% 0.46/0.69  thf('51', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.46/0.69      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.69  thf('52', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.46/0.69      inference('sup-', [status(thm)], ['50', '51'])).
% 0.46/0.69  thf('53', plain,
% 0.46/0.69      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.46/0.69         | ((sk_C_2) = (k1_xboole_0))
% 0.46/0.69         | ((sk_B_1) = (k1_xboole_0))
% 0.46/0.69         | ((sk_A) = (k1_xboole_0))))
% 0.46/0.69         <= (~
% 0.46/0.69             ((r2_hidden @ 
% 0.46/0.69               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ sk_H)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['39', '52'])).
% 0.46/0.69  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.46/0.69  thf('54', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.69      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.69  thf('55', plain,
% 0.46/0.69      (((((sk_C_2) = (k1_xboole_0))
% 0.46/0.69         | ((sk_B_1) = (k1_xboole_0))
% 0.46/0.69         | ((sk_A) = (k1_xboole_0))))
% 0.46/0.69         <= (~
% 0.46/0.69             ((r2_hidden @ 
% 0.46/0.69               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ sk_H)))),
% 0.46/0.69      inference('demod', [status(thm)], ['53', '54'])).
% 0.46/0.69  thf('56', plain,
% 0.46/0.69      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.46/0.69      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.69  thf('57', plain, ((m1_subset_1 @ sk_G @ (k1_zfmisc_1 @ sk_C_2))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('58', plain,
% 0.46/0.69      (![X13 : $i, X14 : $i]:
% 0.46/0.69         ((r2_hidden @ X13 @ X14)
% 0.46/0.69          | (v1_xboole_0 @ X14)
% 0.46/0.69          | ~ (m1_subset_1 @ X13 @ X14))),
% 0.46/0.69      inference('cnf', [status(esa)], [t2_subset])).
% 0.46/0.69  thf('59', plain,
% 0.46/0.69      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_C_2))
% 0.46/0.69        | (r2_hidden @ sk_G @ (k1_zfmisc_1 @ sk_C_2)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['57', '58'])).
% 0.46/0.69  thf('60', plain, (![X12 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.46/0.69      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.46/0.69  thf('61', plain, ((r2_hidden @ sk_G @ (k1_zfmisc_1 @ sk_C_2))),
% 0.46/0.69      inference('clc', [status(thm)], ['59', '60'])).
% 0.46/0.69  thf('62', plain,
% 0.46/0.69      (![X8 : $i, X10 : $i]:
% 0.46/0.69         ((r1_tarski @ X10 @ X8) | ~ (r2_hidden @ X10 @ (k1_zfmisc_1 @ X8)))),
% 0.46/0.69      inference('simplify', [status(thm)], ['16'])).
% 0.46/0.69  thf('63', plain, ((r1_tarski @ sk_G @ sk_C_2)),
% 0.46/0.69      inference('sup-', [status(thm)], ['61', '62'])).
% 0.46/0.69  thf('64', plain,
% 0.46/0.69      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.46/0.69         (~ (r2_hidden @ X3 @ X4)
% 0.46/0.69          | (r2_hidden @ X3 @ X5)
% 0.46/0.69          | ~ (r1_tarski @ X4 @ X5))),
% 0.46/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.69  thf('65', plain,
% 0.46/0.69      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_2) | ~ (r2_hidden @ X0 @ sk_G))),
% 0.46/0.69      inference('sup-', [status(thm)], ['63', '64'])).
% 0.46/0.69  thf('66', plain,
% 0.46/0.69      (((v1_xboole_0 @ sk_G) | (r2_hidden @ (sk_B @ sk_G) @ sk_C_2))),
% 0.46/0.69      inference('sup-', [status(thm)], ['56', '65'])).
% 0.46/0.69  thf('67', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.46/0.69      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.69  thf('68', plain, (((v1_xboole_0 @ sk_G) | ~ (v1_xboole_0 @ sk_C_2))),
% 0.46/0.69      inference('sup-', [status(thm)], ['66', '67'])).
% 0.46/0.69  thf('69', plain,
% 0.46/0.69      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.46/0.69         | ((sk_A) = (k1_xboole_0))
% 0.46/0.69         | ((sk_B_1) = (k1_xboole_0))
% 0.46/0.69         | (v1_xboole_0 @ sk_G)))
% 0.46/0.69         <= (~
% 0.46/0.69             ((r2_hidden @ 
% 0.46/0.69               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ sk_H)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['55', '68'])).
% 0.46/0.69  thf('70', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.69      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.69  thf('71', plain,
% 0.46/0.69      (((((sk_A) = (k1_xboole_0))
% 0.46/0.69         | ((sk_B_1) = (k1_xboole_0))
% 0.46/0.69         | (v1_xboole_0 @ sk_G)))
% 0.46/0.69         <= (~
% 0.46/0.69             ((r2_hidden @ 
% 0.46/0.69               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ sk_H)))),
% 0.46/0.69      inference('demod', [status(thm)], ['69', '70'])).
% 0.46/0.69  thf('72', plain,
% 0.46/0.69      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.69         ((k3_zfmisc_1 @ X15 @ X16 @ X17)
% 0.46/0.69           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16) @ X17))),
% 0.46/0.69      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.46/0.69  thf('73', plain,
% 0.46/0.69      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.46/0.69      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.69  thf('74', plain,
% 0.46/0.69      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.46/0.69         ((r2_hidden @ (k2_mcart_1 @ X22) @ X24)
% 0.46/0.69          | ~ (r2_hidden @ X22 @ (k2_zfmisc_1 @ X23 @ X24)))),
% 0.46/0.69      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.46/0.69  thf('75', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]:
% 0.46/0.69         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.46/0.69          | (r2_hidden @ (k2_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0))) @ X0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['73', '74'])).
% 0.46/0.69  thf('76', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.46/0.69      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.69  thf('77', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]:
% 0.46/0.69         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['75', '76'])).
% 0.46/0.69  thf('78', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.69         ((v1_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.69      inference('sup+', [status(thm)], ['72', '77'])).
% 0.46/0.69  thf('79', plain,
% 0.46/0.69      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.69         ((k4_zfmisc_1 @ X18 @ X19 @ X20 @ X21)
% 0.46/0.69           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X18 @ X19 @ X20) @ X21))),
% 0.46/0.69      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.46/0.69  thf('80', plain,
% 0.46/0.69      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.46/0.69      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.69  thf('81', plain,
% 0.46/0.69      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.46/0.69         ((r2_hidden @ (k1_mcart_1 @ X22) @ X23)
% 0.46/0.69          | ~ (r2_hidden @ X22 @ (k2_zfmisc_1 @ X23 @ X24)))),
% 0.46/0.69      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.46/0.69  thf('82', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]:
% 0.46/0.69         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.46/0.69          | (r2_hidden @ (k1_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0))) @ X1))),
% 0.46/0.69      inference('sup-', [status(thm)], ['80', '81'])).
% 0.46/0.69  thf('83', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.46/0.69      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.69  thf('84', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]:
% 0.46/0.69         ((v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['82', '83'])).
% 0.46/0.69  thf('85', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.69         ((v1_xboole_0 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.46/0.69          | ~ (v1_xboole_0 @ (k3_zfmisc_1 @ X3 @ X2 @ X1)))),
% 0.46/0.69      inference('sup+', [status(thm)], ['79', '84'])).
% 0.46/0.69  thf('86', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.69         (~ (v1_xboole_0 @ X0)
% 0.46/0.69          | (v1_xboole_0 @ (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['78', '85'])).
% 0.46/0.69  thf('87', plain,
% 0.46/0.69      ((r2_hidden @ sk_I @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('88', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.46/0.69      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.69  thf('89', plain,
% 0.46/0.69      (~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.46/0.69      inference('sup-', [status(thm)], ['87', '88'])).
% 0.46/0.69  thf('90', plain, (~ (v1_xboole_0 @ sk_G)),
% 0.46/0.69      inference('sup-', [status(thm)], ['86', '89'])).
% 0.46/0.69  thf('91', plain,
% 0.46/0.69      (((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.46/0.69         <= (~
% 0.46/0.69             ((r2_hidden @ 
% 0.46/0.69               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ sk_H)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['71', '90'])).
% 0.46/0.69  thf('92', plain,
% 0.46/0.69      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.46/0.69      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.69  thf('93', plain, ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ sk_B_1))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('94', plain,
% 0.46/0.69      (![X13 : $i, X14 : $i]:
% 0.46/0.69         ((r2_hidden @ X13 @ X14)
% 0.46/0.69          | (v1_xboole_0 @ X14)
% 0.46/0.69          | ~ (m1_subset_1 @ X13 @ X14))),
% 0.46/0.69      inference('cnf', [status(esa)], [t2_subset])).
% 0.46/0.69  thf('95', plain,
% 0.46/0.69      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_B_1))
% 0.46/0.69        | (r2_hidden @ sk_F @ (k1_zfmisc_1 @ sk_B_1)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['93', '94'])).
% 0.46/0.69  thf('96', plain, (![X12 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.46/0.69      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.46/0.69  thf('97', plain, ((r2_hidden @ sk_F @ (k1_zfmisc_1 @ sk_B_1))),
% 0.46/0.69      inference('clc', [status(thm)], ['95', '96'])).
% 0.46/0.69  thf('98', plain,
% 0.46/0.69      (![X8 : $i, X10 : $i]:
% 0.46/0.69         ((r1_tarski @ X10 @ X8) | ~ (r2_hidden @ X10 @ (k1_zfmisc_1 @ X8)))),
% 0.46/0.69      inference('simplify', [status(thm)], ['16'])).
% 0.46/0.69  thf('99', plain, ((r1_tarski @ sk_F @ sk_B_1)),
% 0.46/0.69      inference('sup-', [status(thm)], ['97', '98'])).
% 0.46/0.69  thf('100', plain,
% 0.46/0.69      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.46/0.69         (~ (r2_hidden @ X3 @ X4)
% 0.46/0.69          | (r2_hidden @ X3 @ X5)
% 0.46/0.69          | ~ (r1_tarski @ X4 @ X5))),
% 0.46/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.69  thf('101', plain,
% 0.46/0.69      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B_1) | ~ (r2_hidden @ X0 @ sk_F))),
% 0.46/0.69      inference('sup-', [status(thm)], ['99', '100'])).
% 0.46/0.69  thf('102', plain,
% 0.46/0.69      (((v1_xboole_0 @ sk_F) | (r2_hidden @ (sk_B @ sk_F) @ sk_B_1))),
% 0.46/0.69      inference('sup-', [status(thm)], ['92', '101'])).
% 0.46/0.69  thf('103', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.46/0.69      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.69  thf('104', plain, (((v1_xboole_0 @ sk_F) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.46/0.69      inference('sup-', [status(thm)], ['102', '103'])).
% 0.46/0.69  thf('105', plain,
% 0.46/0.69      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.46/0.69         | ((sk_A) = (k1_xboole_0))
% 0.46/0.69         | (v1_xboole_0 @ sk_F)))
% 0.46/0.69         <= (~
% 0.46/0.69             ((r2_hidden @ 
% 0.46/0.69               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ sk_H)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['91', '104'])).
% 0.46/0.69  thf('106', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.69      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.69  thf('107', plain,
% 0.46/0.69      (((((sk_A) = (k1_xboole_0)) | (v1_xboole_0 @ sk_F)))
% 0.46/0.69         <= (~
% 0.46/0.69             ((r2_hidden @ 
% 0.46/0.69               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ sk_H)))),
% 0.46/0.69      inference('demod', [status(thm)], ['105', '106'])).
% 0.46/0.69  thf('108', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]:
% 0.46/0.69         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['75', '76'])).
% 0.46/0.69  thf('109', plain,
% 0.46/0.69      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.69         ((k3_zfmisc_1 @ X15 @ X16 @ X17)
% 0.46/0.69           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16) @ X17))),
% 0.46/0.69      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.46/0.69  thf('110', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]:
% 0.46/0.69         ((v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['82', '83'])).
% 0.46/0.69  thf('111', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.69         ((v1_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.46/0.69          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.46/0.69      inference('sup+', [status(thm)], ['109', '110'])).
% 0.46/0.69  thf('112', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.69         (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k3_zfmisc_1 @ X1 @ X0 @ X2)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['108', '111'])).
% 0.46/0.69  thf('113', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.69         ((v1_xboole_0 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.46/0.69          | ~ (v1_xboole_0 @ (k3_zfmisc_1 @ X3 @ X2 @ X1)))),
% 0.46/0.69      inference('sup+', [status(thm)], ['79', '84'])).
% 0.46/0.69  thf('114', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.69         (~ (v1_xboole_0 @ X1)
% 0.46/0.69          | (v1_xboole_0 @ (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['112', '113'])).
% 0.46/0.69  thf('115', plain,
% 0.46/0.69      (~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.46/0.69      inference('sup-', [status(thm)], ['87', '88'])).
% 0.46/0.69  thf('116', plain, (~ (v1_xboole_0 @ sk_F)),
% 0.46/0.69      inference('sup-', [status(thm)], ['114', '115'])).
% 0.46/0.69  thf('117', plain,
% 0.46/0.69      ((((sk_A) = (k1_xboole_0)))
% 0.46/0.69         <= (~
% 0.46/0.69             ((r2_hidden @ 
% 0.46/0.69               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ sk_H)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['107', '116'])).
% 0.46/0.69  thf('118', plain,
% 0.46/0.69      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.46/0.69      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.69  thf('119', plain,
% 0.46/0.69      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_E))),
% 0.46/0.69      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.69  thf('120', plain,
% 0.46/0.69      (((v1_xboole_0 @ sk_E) | (r2_hidden @ (sk_B @ sk_E) @ sk_A))),
% 0.46/0.69      inference('sup-', [status(thm)], ['118', '119'])).
% 0.46/0.69  thf('121', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.46/0.69      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.69  thf('122', plain, (((v1_xboole_0 @ sk_E) | ~ (v1_xboole_0 @ sk_A))),
% 0.46/0.69      inference('sup-', [status(thm)], ['120', '121'])).
% 0.46/0.69  thf('123', plain,
% 0.46/0.69      (((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_E)))
% 0.46/0.69         <= (~
% 0.46/0.69             ((r2_hidden @ 
% 0.46/0.69               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ sk_H)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['117', '122'])).
% 0.46/0.69  thf('124', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.69      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.69  thf('125', plain,
% 0.46/0.69      (((v1_xboole_0 @ sk_E))
% 0.46/0.69         <= (~
% 0.46/0.69             ((r2_hidden @ 
% 0.46/0.69               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ sk_H)))),
% 0.46/0.69      inference('demod', [status(thm)], ['123', '124'])).
% 0.46/0.69  thf('126', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]:
% 0.46/0.69         ((v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['82', '83'])).
% 0.46/0.69  thf('127', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.69         ((v1_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.46/0.69          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.46/0.69      inference('sup+', [status(thm)], ['109', '110'])).
% 0.46/0.69  thf('128', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.69         (~ (v1_xboole_0 @ X1) | (v1_xboole_0 @ (k3_zfmisc_1 @ X1 @ X0 @ X2)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['126', '127'])).
% 0.46/0.69  thf('129', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.69         ((v1_xboole_0 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.46/0.69          | ~ (v1_xboole_0 @ (k3_zfmisc_1 @ X3 @ X2 @ X1)))),
% 0.46/0.69      inference('sup+', [status(thm)], ['79', '84'])).
% 0.46/0.69  thf('130', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.69         (~ (v1_xboole_0 @ X2)
% 0.46/0.69          | (v1_xboole_0 @ (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['128', '129'])).
% 0.46/0.69  thf('131', plain,
% 0.46/0.69      (~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.46/0.69      inference('sup-', [status(thm)], ['87', '88'])).
% 0.46/0.69  thf('132', plain, (~ (v1_xboole_0 @ sk_E)),
% 0.46/0.69      inference('sup-', [status(thm)], ['130', '131'])).
% 0.46/0.69  thf('133', plain,
% 0.46/0.69      (((r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ 
% 0.46/0.69         sk_H))),
% 0.46/0.69      inference('sup-', [status(thm)], ['125', '132'])).
% 0.46/0.69  thf('134', plain,
% 0.46/0.69      ((m1_subset_1 @ sk_I @ (k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('135', plain,
% 0.46/0.69      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.46/0.69         (((X25) = (k1_xboole_0))
% 0.46/0.69          | ((X26) = (k1_xboole_0))
% 0.46/0.69          | ((X27) = (k1_xboole_0))
% 0.46/0.69          | ((k10_mcart_1 @ X25 @ X26 @ X27 @ X29 @ X28)
% 0.46/0.69              = (k2_mcart_1 @ (k1_mcart_1 @ X28)))
% 0.46/0.69          | ~ (m1_subset_1 @ X28 @ (k4_zfmisc_1 @ X25 @ X26 @ X27 @ X29))
% 0.46/0.69          | ((X29) = (k1_xboole_0)))),
% 0.46/0.69      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.46/0.69  thf('136', plain,
% 0.46/0.69      ((((sk_D) = (k1_xboole_0))
% 0.46/0.69        | ((k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I)
% 0.46/0.69            = (k2_mcart_1 @ (k1_mcart_1 @ sk_I)))
% 0.46/0.69        | ((sk_C_2) = (k1_xboole_0))
% 0.46/0.69        | ((sk_B_1) = (k1_xboole_0))
% 0.46/0.69        | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['134', '135'])).
% 0.46/0.69  thf('137', plain,
% 0.46/0.69      ((~ (r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ 
% 0.46/0.69           sk_G))
% 0.46/0.69         <= (~
% 0.46/0.69             ((r2_hidden @ 
% 0.46/0.69               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ sk_G)))),
% 0.46/0.69      inference('split', [status(esa)], ['27'])).
% 0.46/0.69  thf('138', plain,
% 0.46/0.69      (((~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_I)) @ sk_G)
% 0.46/0.69         | ((sk_A) = (k1_xboole_0))
% 0.46/0.69         | ((sk_B_1) = (k1_xboole_0))
% 0.46/0.69         | ((sk_C_2) = (k1_xboole_0))
% 0.46/0.69         | ((sk_D) = (k1_xboole_0))))
% 0.46/0.69         <= (~
% 0.46/0.69             ((r2_hidden @ 
% 0.46/0.69               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ sk_G)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['136', '137'])).
% 0.46/0.69  thf('139', plain,
% 0.46/0.69      ((r2_hidden @ (k1_mcart_1 @ sk_I) @ (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G))),
% 0.46/0.69      inference('sup-', [status(thm)], ['0', '3'])).
% 0.46/0.69  thf('140', plain,
% 0.46/0.69      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.69         ((k3_zfmisc_1 @ X15 @ X16 @ X17)
% 0.46/0.69           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16) @ X17))),
% 0.46/0.69      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.46/0.69  thf('141', plain,
% 0.46/0.69      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.46/0.69         ((r2_hidden @ (k2_mcart_1 @ X22) @ X24)
% 0.46/0.69          | ~ (r2_hidden @ X22 @ (k2_zfmisc_1 @ X23 @ X24)))),
% 0.46/0.69      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.46/0.69  thf('142', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.69         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.46/0.69          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['140', '141'])).
% 0.46/0.69  thf('143', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_I)) @ sk_G)),
% 0.46/0.69      inference('sup-', [status(thm)], ['139', '142'])).
% 0.46/0.69  thf('144', plain,
% 0.46/0.69      (((((sk_A) = (k1_xboole_0))
% 0.46/0.69         | ((sk_B_1) = (k1_xboole_0))
% 0.46/0.69         | ((sk_C_2) = (k1_xboole_0))
% 0.46/0.69         | ((sk_D) = (k1_xboole_0))))
% 0.46/0.69         <= (~
% 0.46/0.69             ((r2_hidden @ 
% 0.46/0.69               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ sk_G)))),
% 0.46/0.69      inference('demod', [status(thm)], ['138', '143'])).
% 0.46/0.69  thf('145', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.46/0.69      inference('sup-', [status(thm)], ['50', '51'])).
% 0.46/0.69  thf('146', plain,
% 0.46/0.69      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.46/0.69         | ((sk_C_2) = (k1_xboole_0))
% 0.46/0.69         | ((sk_B_1) = (k1_xboole_0))
% 0.46/0.69         | ((sk_A) = (k1_xboole_0))))
% 0.46/0.69         <= (~
% 0.46/0.69             ((r2_hidden @ 
% 0.46/0.69               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ sk_G)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['144', '145'])).
% 0.46/0.69  thf('147', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.69      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.69  thf('148', plain,
% 0.46/0.69      (((((sk_C_2) = (k1_xboole_0))
% 0.46/0.69         | ((sk_B_1) = (k1_xboole_0))
% 0.46/0.69         | ((sk_A) = (k1_xboole_0))))
% 0.46/0.69         <= (~
% 0.46/0.69             ((r2_hidden @ 
% 0.46/0.69               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ sk_G)))),
% 0.46/0.69      inference('demod', [status(thm)], ['146', '147'])).
% 0.46/0.69  thf('149', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_I)) @ sk_G)),
% 0.46/0.69      inference('sup-', [status(thm)], ['139', '142'])).
% 0.46/0.69  thf('150', plain,
% 0.46/0.69      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_2) | ~ (r2_hidden @ X0 @ sk_G))),
% 0.46/0.69      inference('sup-', [status(thm)], ['63', '64'])).
% 0.46/0.69  thf('151', plain,
% 0.46/0.69      ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_I)) @ sk_C_2)),
% 0.46/0.69      inference('sup-', [status(thm)], ['149', '150'])).
% 0.46/0.69  thf('152', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.46/0.69      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.69  thf('153', plain, (~ (v1_xboole_0 @ sk_C_2)),
% 0.46/0.69      inference('sup-', [status(thm)], ['151', '152'])).
% 0.46/0.69  thf('154', plain,
% 0.46/0.69      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.46/0.69         | ((sk_A) = (k1_xboole_0))
% 0.46/0.69         | ((sk_B_1) = (k1_xboole_0))))
% 0.46/0.69         <= (~
% 0.46/0.69             ((r2_hidden @ 
% 0.46/0.69               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ sk_G)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['148', '153'])).
% 0.46/0.69  thf('155', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.69      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.69  thf('156', plain,
% 0.46/0.69      (((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0))))
% 0.46/0.69         <= (~
% 0.46/0.69             ((r2_hidden @ 
% 0.46/0.69               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ sk_G)))),
% 0.46/0.69      inference('demod', [status(thm)], ['154', '155'])).
% 0.46/0.69  thf('157', plain,
% 0.46/0.69      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I)) @ 
% 0.46/0.69        (k2_zfmisc_1 @ sk_E @ sk_F))),
% 0.46/0.69      inference('sup-', [status(thm)], ['4', '7'])).
% 0.46/0.69  thf('158', plain,
% 0.46/0.69      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.46/0.69         ((r2_hidden @ (k2_mcart_1 @ X22) @ X24)
% 0.46/0.69          | ~ (r2_hidden @ X22 @ (k2_zfmisc_1 @ X23 @ X24)))),
% 0.46/0.69      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.46/0.69  thf('159', plain,
% 0.46/0.69      ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ sk_F)),
% 0.46/0.69      inference('sup-', [status(thm)], ['157', '158'])).
% 0.46/0.69  thf('160', plain,
% 0.46/0.69      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B_1) | ~ (r2_hidden @ X0 @ sk_F))),
% 0.46/0.69      inference('sup-', [status(thm)], ['99', '100'])).
% 0.46/0.69  thf('161', plain,
% 0.46/0.69      ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ sk_B_1)),
% 0.46/0.69      inference('sup-', [status(thm)], ['159', '160'])).
% 0.46/0.69  thf('162', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.46/0.69      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.69  thf('163', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.46/0.69      inference('sup-', [status(thm)], ['161', '162'])).
% 0.46/0.69  thf('164', plain,
% 0.46/0.69      (((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_A) = (k1_xboole_0))))
% 0.46/0.69         <= (~
% 0.46/0.69             ((r2_hidden @ 
% 0.46/0.69               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ sk_G)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['156', '163'])).
% 0.46/0.69  thf('165', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.69      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.69  thf('166', plain,
% 0.46/0.69      ((((sk_A) = (k1_xboole_0)))
% 0.46/0.69         <= (~
% 0.46/0.69             ((r2_hidden @ 
% 0.46/0.69               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ sk_G)))),
% 0.46/0.69      inference('demod', [status(thm)], ['164', '165'])).
% 0.46/0.69  thf('167', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.46/0.69      inference('sup-', [status(thm)], ['21', '22'])).
% 0.46/0.69  thf('168', plain,
% 0.46/0.69      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.46/0.69         <= (~
% 0.46/0.69             ((r2_hidden @ 
% 0.46/0.69               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ sk_G)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['166', '167'])).
% 0.46/0.69  thf('169', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.69      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.69  thf('170', plain,
% 0.46/0.69      (((r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ 
% 0.46/0.69         sk_G))),
% 0.46/0.69      inference('demod', [status(thm)], ['168', '169'])).
% 0.46/0.69  thf('171', plain,
% 0.46/0.69      ((m1_subset_1 @ sk_I @ (k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('172', plain,
% 0.46/0.69      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.46/0.69         (((X25) = (k1_xboole_0))
% 0.46/0.69          | ((X26) = (k1_xboole_0))
% 0.46/0.69          | ((X27) = (k1_xboole_0))
% 0.46/0.69          | ((k9_mcart_1 @ X25 @ X26 @ X27 @ X29 @ X28)
% 0.46/0.69              = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ X28))))
% 0.46/0.69          | ~ (m1_subset_1 @ X28 @ (k4_zfmisc_1 @ X25 @ X26 @ X27 @ X29))
% 0.46/0.69          | ((X29) = (k1_xboole_0)))),
% 0.46/0.69      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.46/0.69  thf('173', plain,
% 0.46/0.69      ((((sk_D) = (k1_xboole_0))
% 0.46/0.69        | ((k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I)
% 0.46/0.69            = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))))
% 0.46/0.69        | ((sk_C_2) = (k1_xboole_0))
% 0.46/0.69        | ((sk_B_1) = (k1_xboole_0))
% 0.46/0.69        | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['171', '172'])).
% 0.46/0.69  thf('174', plain,
% 0.46/0.69      ((~ (r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ 
% 0.46/0.69           sk_F))
% 0.46/0.69         <= (~
% 0.46/0.69             ((r2_hidden @ 
% 0.46/0.69               (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ sk_F)))),
% 0.46/0.69      inference('split', [status(esa)], ['27'])).
% 0.46/0.69  thf('175', plain,
% 0.46/0.69      (((~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ 
% 0.46/0.69            sk_F)
% 0.46/0.69         | ((sk_A) = (k1_xboole_0))
% 0.46/0.69         | ((sk_B_1) = (k1_xboole_0))
% 0.46/0.69         | ((sk_C_2) = (k1_xboole_0))
% 0.46/0.69         | ((sk_D) = (k1_xboole_0))))
% 0.46/0.69         <= (~
% 0.46/0.69             ((r2_hidden @ 
% 0.46/0.69               (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ sk_F)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['173', '174'])).
% 0.46/0.69  thf('176', plain,
% 0.46/0.69      ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ sk_F)),
% 0.46/0.69      inference('sup-', [status(thm)], ['157', '158'])).
% 0.46/0.69  thf('177', plain,
% 0.46/0.69      (((((sk_A) = (k1_xboole_0))
% 0.46/0.69         | ((sk_B_1) = (k1_xboole_0))
% 0.46/0.69         | ((sk_C_2) = (k1_xboole_0))
% 0.46/0.69         | ((sk_D) = (k1_xboole_0))))
% 0.46/0.69         <= (~
% 0.46/0.69             ((r2_hidden @ 
% 0.46/0.69               (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ sk_F)))),
% 0.46/0.69      inference('demod', [status(thm)], ['175', '176'])).
% 0.46/0.69  thf('178', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.46/0.69      inference('sup-', [status(thm)], ['50', '51'])).
% 0.46/0.69  thf('179', plain,
% 0.46/0.69      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.46/0.69         | ((sk_C_2) = (k1_xboole_0))
% 0.46/0.69         | ((sk_B_1) = (k1_xboole_0))
% 0.46/0.69         | ((sk_A) = (k1_xboole_0))))
% 0.46/0.69         <= (~
% 0.46/0.69             ((r2_hidden @ 
% 0.46/0.69               (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ sk_F)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['177', '178'])).
% 0.46/0.69  thf('180', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.69      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.69  thf('181', plain,
% 0.46/0.69      (((((sk_C_2) = (k1_xboole_0))
% 0.46/0.69         | ((sk_B_1) = (k1_xboole_0))
% 0.46/0.69         | ((sk_A) = (k1_xboole_0))))
% 0.46/0.69         <= (~
% 0.46/0.69             ((r2_hidden @ 
% 0.46/0.69               (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ sk_F)))),
% 0.46/0.69      inference('demod', [status(thm)], ['179', '180'])).
% 0.46/0.69  thf('182', plain, (~ (v1_xboole_0 @ sk_C_2)),
% 0.46/0.69      inference('sup-', [status(thm)], ['151', '152'])).
% 0.46/0.69  thf('183', plain,
% 0.46/0.69      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.46/0.69         | ((sk_A) = (k1_xboole_0))
% 0.46/0.69         | ((sk_B_1) = (k1_xboole_0))))
% 0.46/0.69         <= (~
% 0.46/0.69             ((r2_hidden @ 
% 0.46/0.69               (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ sk_F)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['181', '182'])).
% 0.46/0.69  thf('184', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.69      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.69  thf('185', plain,
% 0.46/0.69      (((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0))))
% 0.46/0.69         <= (~
% 0.46/0.69             ((r2_hidden @ 
% 0.46/0.69               (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ sk_F)))),
% 0.46/0.69      inference('demod', [status(thm)], ['183', '184'])).
% 0.46/0.69  thf('186', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.46/0.69      inference('sup-', [status(thm)], ['161', '162'])).
% 0.46/0.69  thf('187', plain,
% 0.46/0.69      (((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_A) = (k1_xboole_0))))
% 0.46/0.69         <= (~
% 0.46/0.69             ((r2_hidden @ 
% 0.46/0.69               (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ sk_F)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['185', '186'])).
% 0.46/0.69  thf('188', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.69      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.69  thf('189', plain,
% 0.46/0.69      ((((sk_A) = (k1_xboole_0)))
% 0.46/0.69         <= (~
% 0.46/0.69             ((r2_hidden @ 
% 0.46/0.69               (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ sk_F)))),
% 0.46/0.69      inference('demod', [status(thm)], ['187', '188'])).
% 0.46/0.69  thf('190', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.46/0.69      inference('sup-', [status(thm)], ['21', '22'])).
% 0.46/0.69  thf('191', plain,
% 0.46/0.69      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.46/0.69         <= (~
% 0.46/0.69             ((r2_hidden @ 
% 0.46/0.69               (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ sk_F)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['189', '190'])).
% 0.46/0.69  thf('192', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.69      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.69  thf('193', plain,
% 0.46/0.69      (((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ sk_F))),
% 0.46/0.69      inference('demod', [status(thm)], ['191', '192'])).
% 0.46/0.69  thf('194', plain,
% 0.46/0.69      (~
% 0.46/0.69       ((r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ sk_E)) | 
% 0.46/0.69       ~
% 0.46/0.69       ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ sk_F)) | 
% 0.46/0.69       ~
% 0.46/0.69       ((r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ 
% 0.46/0.69         sk_G)) | 
% 0.46/0.69       ~
% 0.46/0.69       ((r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ 
% 0.46/0.69         sk_H))),
% 0.46/0.69      inference('split', [status(esa)], ['27'])).
% 0.46/0.69  thf('195', plain,
% 0.46/0.69      (~
% 0.46/0.69       ((r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ sk_E))),
% 0.46/0.69      inference('sat_resolution*', [status(thm)], ['133', '170', '193', '194'])).
% 0.46/0.69  thf('196', plain,
% 0.46/0.69      (~ (r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_I) @ 
% 0.46/0.69          sk_E)),
% 0.46/0.69      inference('simpl_trail', [status(thm)], ['28', '195'])).
% 0.46/0.69  thf('197', plain,
% 0.46/0.69      ((~ (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ sk_E)
% 0.46/0.69        | ((sk_A) = (k1_xboole_0))
% 0.46/0.69        | ((sk_B_1) = (k1_xboole_0))
% 0.46/0.69        | ((sk_C_2) = (k1_xboole_0))
% 0.46/0.69        | ((sk_D) = (k1_xboole_0)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['26', '196'])).
% 0.46/0.69  thf('198', plain,
% 0.46/0.69      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ sk_E)),
% 0.46/0.69      inference('sup-', [status(thm)], ['8', '9'])).
% 0.46/0.69  thf('199', plain,
% 0.46/0.69      ((((sk_A) = (k1_xboole_0))
% 0.46/0.69        | ((sk_B_1) = (k1_xboole_0))
% 0.46/0.69        | ((sk_C_2) = (k1_xboole_0))
% 0.46/0.69        | ((sk_D) = (k1_xboole_0)))),
% 0.46/0.69      inference('demod', [status(thm)], ['197', '198'])).
% 0.46/0.69  thf('200', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.46/0.69      inference('sup-', [status(thm)], ['50', '51'])).
% 0.46/0.69  thf('201', plain,
% 0.46/0.69      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.46/0.69        | ((sk_C_2) = (k1_xboole_0))
% 0.46/0.69        | ((sk_B_1) = (k1_xboole_0))
% 0.46/0.69        | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['199', '200'])).
% 0.46/0.69  thf('202', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.69      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.69  thf('203', plain,
% 0.46/0.69      ((((sk_C_2) = (k1_xboole_0))
% 0.46/0.69        | ((sk_B_1) = (k1_xboole_0))
% 0.46/0.69        | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.69      inference('demod', [status(thm)], ['201', '202'])).
% 0.46/0.69  thf('204', plain, (~ (v1_xboole_0 @ sk_C_2)),
% 0.46/0.69      inference('sup-', [status(thm)], ['151', '152'])).
% 0.46/0.69  thf('205', plain,
% 0.46/0.69      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.46/0.69        | ((sk_A) = (k1_xboole_0))
% 0.46/0.69        | ((sk_B_1) = (k1_xboole_0)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['203', '204'])).
% 0.46/0.69  thf('206', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.69      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.69  thf('207', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.46/0.69      inference('demod', [status(thm)], ['205', '206'])).
% 0.46/0.69  thf('208', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.46/0.69      inference('sup-', [status(thm)], ['161', '162'])).
% 0.46/0.69  thf('209', plain,
% 0.46/0.69      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['207', '208'])).
% 0.46/0.69  thf('210', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.69      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.69  thf('211', plain, (((sk_A) = (k1_xboole_0))),
% 0.46/0.69      inference('demod', [status(thm)], ['209', '210'])).
% 0.46/0.69  thf('212', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.69      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.69  thf('213', plain, ($false),
% 0.46/0.69      inference('demod', [status(thm)], ['23', '211', '212'])).
% 0.46/0.69  
% 0.46/0.69  % SZS output end Refutation
% 0.46/0.69  
% 0.46/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
