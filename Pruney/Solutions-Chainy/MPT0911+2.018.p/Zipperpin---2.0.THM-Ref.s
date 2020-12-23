%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.d9GCtu4w8W

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:58 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :  197 ( 413 expanded)
%              Number of leaves         :   37 ( 142 expanded)
%              Depth                    :   28
%              Number of atoms          : 1746 (5790 expanded)
%              Number of equality atoms :  230 ( 750 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(t71_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( ! [F: $i] :
            ( ( m1_subset_1 @ F @ A )
           => ! [G: $i] :
                ( ( m1_subset_1 @ G @ B )
               => ! [H: $i] :
                    ( ( m1_subset_1 @ H @ C )
                   => ( ( E
                        = ( k3_mcart_1 @ F @ G @ H ) )
                     => ( D = H ) ) ) ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( C = k1_xboole_0 )
          | ( D
            = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) )
       => ( ! [F: $i] :
              ( ( m1_subset_1 @ F @ A )
             => ! [G: $i] :
                  ( ( m1_subset_1 @ G @ B )
                 => ! [H: $i] :
                      ( ( m1_subset_1 @ H @ C )
                     => ( ( E
                          = ( k3_mcart_1 @ F @ G @ H ) )
                       => ( D = H ) ) ) ) )
         => ( ( A = k1_xboole_0 )
            | ( B = k1_xboole_0 )
            | ( C = k1_xboole_0 )
            | ( D
              = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t71_mcart_1])).

thf('0',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('1',plain,(
    ! [X35: $i] :
      ( ( X35 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X35 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X21 ) @ X22 )
      | ~ ( r2_hidden @ X21 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( sk_B_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t23_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( A
          = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ) )).

thf('9',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X24
        = ( k4_tarski @ ( k1_mcart_1 @ X24 ) @ ( k2_mcart_1 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X25 )
      | ~ ( r2_hidden @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('10',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('11',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_zfmisc_1 @ X14 @ X15 @ X16 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( v1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X35: $i] :
      ( ( X35 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X35 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('19',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k4_zfmisc_1 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X17 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t55_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 ) )
    <=> ( ( k4_zfmisc_1 @ A @ B @ C @ D )
       != k1_xboole_0 ) ) )).

thf('21',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( ( k4_zfmisc_1 @ X30 @ X31 @ X32 @ X33 )
       != k1_xboole_0 )
      | ( X33 = k1_xboole_0 )
      | ( X32 = k1_xboole_0 )
      | ( X31 = k1_xboole_0 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['22','23','24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['5','26'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('28',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( k1_xboole_0 != sk_E )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference(eq_fact,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('33',plain,
    ( sk_E
    = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('35',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_zfmisc_1 @ X14 @ X15 @ X16 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('36',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X21 ) @ X22 )
      | ~ ( r2_hidden @ X21 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X24
        = ( k4_tarski @ ( k1_mcart_1 @ X24 ) @ ( k2_mcart_1 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X25 )
      | ~ ( r2_hidden @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('44',plain,
    ( ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('45',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_mcart_1 @ X11 @ X12 @ X13 )
      = ( k4_tarski @ ( k4_tarski @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X0 )
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('48',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X21 ) @ X23 )
      | ~ ( r2_hidden @ X21 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('49',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('51',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k4_zfmisc_1 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X17 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X30: $i,X31: $i,X32: $i,X34: $i] :
      ( ( X32 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X30 @ X31 @ X32 @ X34 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('55',plain,(
    ! [X30: $i,X31: $i,X34: $i] :
      ( ( k4_zfmisc_1 @ X30 @ X31 @ k1_xboole_0 @ X34 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_zfmisc_1 @ X14 @ X15 @ X16 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('57',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_zfmisc_1 @ X14 @ X15 @ X16 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k4_zfmisc_1 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X17 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k4_zfmisc_1 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X17 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 @ X4 )
      = ( k2_zfmisc_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) @ X4 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','62'])).

thf('64',plain,(
    ! [X30: $i,X31: $i,X32: $i,X34: $i] :
      ( ( X34 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X30 @ X31 @ X32 @ X34 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('65',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( k4_zfmisc_1 @ X30 @ X31 @ X32 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['63','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['53','66'])).

thf('68',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( ( k4_zfmisc_1 @ X30 @ X31 @ X32 @ X33 )
       != k1_xboole_0 )
      | ( X33 = k1_xboole_0 )
      | ( X32 = k1_xboole_0 )
      | ( X31 = k1_xboole_0 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['70','71','72','73'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('75',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ X5 @ X6 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf(fc1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( v1_xboole_0 @ ( k4_tarski @ A @ B ) ) )).

thf('79',plain,(
    ! [X3: $i,X4: $i] :
      ~ ( v1_xboole_0 @ ( k4_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc1_zfmisc_1])).

thf('80',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X41 @ sk_B_2 )
      | ( sk_E
       != ( k3_mcart_1 @ X42 @ X41 @ X43 ) )
      | ( sk_D = X43 )
      | ~ ( m1_subset_1 @ X43 @ sk_C )
      | ~ ( m1_subset_1 @ X42 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_D = X1 )
      | ( sk_E
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
        = k1_xboole_0 )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','82'])).

thf('84',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('85',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X21 ) @ X22 )
      | ~ ( r2_hidden @ X21 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('86',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('88',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k4_zfmisc_1 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X17 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['63','65'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( ( k4_zfmisc_1 @ X30 @ X31 @ X32 @ X33 )
       != k1_xboole_0 )
      | ( X33 = k1_xboole_0 )
      | ( X32 = k1_xboole_0 )
      | ( X31 = k1_xboole_0 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['95','96','97','98'])).

thf('100',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ X5 @ X6 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X3: $i,X4: $i] :
      ~ ( v1_xboole_0 @ ( k4_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc1_zfmisc_1])).

thf('105',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
        = k1_xboole_0 )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['83','105'])).

thf('107',plain,
    ( ( sk_E != sk_E )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('109',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('110',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_zfmisc_1 @ X14 @ X15 @ X16 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('111',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X21 ) @ X23 )
      | ~ ( r2_hidden @ X21 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['109','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('115',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k4_zfmisc_1 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X17 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( ( k4_zfmisc_1 @ X30 @ X31 @ X32 @ X33 )
       != k1_xboole_0 )
      | ( X33 = k1_xboole_0 )
      | ( X32 = k1_xboole_0 )
      | ( X31 = k1_xboole_0 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['119','120','121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['108','123'])).

thf('125',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ X5 @ X6 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X3: $i,X4: $i] :
      ~ ( v1_xboole_0 @ ( k4_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc1_zfmisc_1])).

thf('133',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,
    ( ( sk_E != sk_E )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['107','133'])).

thf('135',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    sk_D
 != ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( ( ( k5_mcart_1 @ A @ B @ C @ D )
                  = ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) )
                & ( ( k6_mcart_1 @ A @ B @ C @ D )
                  = ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) )
                & ( ( k7_mcart_1 @ A @ B @ C @ D )
                  = ( k2_mcart_1 @ D ) ) ) ) ) )).

thf('138',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X26 = k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X26 @ X27 @ X29 @ X28 )
        = ( k2_mcart_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k3_zfmisc_1 @ X26 @ X27 @ X29 ) )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('139',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E )
      = ( k2_mcart_1 @ sk_E ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['139','140','141','142'])).

thf('144',plain,(
    sk_D
 != ( k2_mcart_1 @ sk_E ) ),
    inference(demod,[status(thm)],['136','143'])).

thf('145',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['135','144'])).

thf('146',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k4_zfmisc_1 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X17 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['63','65'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( ( k4_zfmisc_1 @ X30 @ X31 @ X32 @ X33 )
       != k1_xboole_0 )
      | ( X33 = k1_xboole_0 )
      | ( X32 = k1_xboole_0 )
      | ( X31 = k1_xboole_0 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['152','153','154','155'])).

thf('157',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','156'])).

thf('158',plain,(
    $false ),
    inference(simplify,[status(thm)],['157'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.d9GCtu4w8W
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:12:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.45/1.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.45/1.64  % Solved by: fo/fo7.sh
% 1.45/1.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.45/1.64  % done 883 iterations in 1.140s
% 1.45/1.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.45/1.64  % SZS output start Refutation
% 1.45/1.64  thf(sk_C_type, type, sk_C: $i).
% 1.45/1.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.45/1.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.45/1.64  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 1.45/1.64  thf(sk_B_2_type, type, sk_B_2: $i).
% 1.45/1.64  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.45/1.64  thf(sk_E_type, type, sk_E: $i).
% 1.45/1.64  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.45/1.64  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 1.45/1.64  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.45/1.64  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 1.45/1.64  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 1.45/1.64  thf(sk_D_type, type, sk_D: $i).
% 1.45/1.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.45/1.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.45/1.64  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 1.45/1.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.45/1.64  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 1.45/1.64  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 1.45/1.64  thf(sk_A_type, type, sk_A: $i).
% 1.45/1.64  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 1.45/1.64  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 1.45/1.64  thf(t71_mcart_1, conjecture,
% 1.45/1.64    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.45/1.64     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.45/1.64       ( ( ![F:$i]:
% 1.45/1.64           ( ( m1_subset_1 @ F @ A ) =>
% 1.45/1.64             ( ![G:$i]:
% 1.45/1.64               ( ( m1_subset_1 @ G @ B ) =>
% 1.45/1.64                 ( ![H:$i]:
% 1.45/1.64                   ( ( m1_subset_1 @ H @ C ) =>
% 1.45/1.64                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 1.45/1.64                       ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 1.45/1.64         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.45/1.64           ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.45/1.64           ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 1.45/1.64  thf(zf_stmt_0, negated_conjecture,
% 1.45/1.64    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.45/1.64        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.45/1.64          ( ( ![F:$i]:
% 1.45/1.64              ( ( m1_subset_1 @ F @ A ) =>
% 1.45/1.64                ( ![G:$i]:
% 1.45/1.64                  ( ( m1_subset_1 @ G @ B ) =>
% 1.45/1.64                    ( ![H:$i]:
% 1.45/1.64                      ( ( m1_subset_1 @ H @ C ) =>
% 1.45/1.64                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 1.45/1.64                          ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 1.45/1.64            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.45/1.64              ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.45/1.64              ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 1.45/1.64    inference('cnf.neg', [status(esa)], [t71_mcart_1])).
% 1.45/1.64  thf('0', plain, (((sk_C) != (k1_xboole_0))),
% 1.45/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.64  thf(t6_mcart_1, axiom,
% 1.45/1.64    (![A:$i]:
% 1.45/1.64     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.45/1.64          ( ![B:$i]:
% 1.45/1.64            ( ~( ( r2_hidden @ B @ A ) & 
% 1.45/1.64                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 1.45/1.64                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 1.45/1.64                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 1.45/1.64                       ( r2_hidden @ G @ B ) ) =>
% 1.45/1.64                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 1.45/1.64  thf('1', plain,
% 1.45/1.64      (![X35 : $i]:
% 1.45/1.64         (((X35) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X35) @ X35))),
% 1.45/1.64      inference('cnf', [status(esa)], [t6_mcart_1])).
% 1.45/1.64  thf(t10_mcart_1, axiom,
% 1.45/1.64    (![A:$i,B:$i,C:$i]:
% 1.45/1.64     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 1.45/1.64       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 1.45/1.64         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 1.45/1.64  thf('2', plain,
% 1.45/1.64      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.45/1.64         ((r2_hidden @ (k1_mcart_1 @ X21) @ X22)
% 1.45/1.64          | ~ (r2_hidden @ X21 @ (k2_zfmisc_1 @ X22 @ X23)))),
% 1.45/1.64      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.45/1.64  thf('3', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 1.45/1.64          | (r2_hidden @ (k1_mcart_1 @ (sk_B_1 @ (k2_zfmisc_1 @ X1 @ X0))) @ X1))),
% 1.45/1.64      inference('sup-', [status(thm)], ['1', '2'])).
% 1.45/1.64  thf(d1_xboole_0, axiom,
% 1.45/1.64    (![A:$i]:
% 1.45/1.64     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.45/1.64  thf('4', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.45/1.64      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.45/1.64  thf('5', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.45/1.64      inference('sup-', [status(thm)], ['3', '4'])).
% 1.45/1.64  thf('6', plain,
% 1.45/1.64      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 1.45/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.64  thf(t2_subset, axiom,
% 1.45/1.64    (![A:$i,B:$i]:
% 1.45/1.64     ( ( m1_subset_1 @ A @ B ) =>
% 1.45/1.64       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 1.45/1.64  thf('7', plain,
% 1.45/1.64      (![X7 : $i, X8 : $i]:
% 1.45/1.64         ((r2_hidden @ X7 @ X8)
% 1.45/1.64          | (v1_xboole_0 @ X8)
% 1.45/1.64          | ~ (m1_subset_1 @ X7 @ X8))),
% 1.45/1.64      inference('cnf', [status(esa)], [t2_subset])).
% 1.45/1.64  thf('8', plain,
% 1.45/1.64      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.45/1.64        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 1.45/1.64      inference('sup-', [status(thm)], ['6', '7'])).
% 1.45/1.64  thf(t23_mcart_1, axiom,
% 1.45/1.64    (![A:$i,B:$i]:
% 1.45/1.64     ( ( v1_relat_1 @ B ) =>
% 1.45/1.64       ( ( r2_hidden @ A @ B ) =>
% 1.45/1.64         ( ( A ) = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ))).
% 1.45/1.64  thf('9', plain,
% 1.45/1.64      (![X24 : $i, X25 : $i]:
% 1.45/1.64         (((X24) = (k4_tarski @ (k1_mcart_1 @ X24) @ (k2_mcart_1 @ X24)))
% 1.45/1.64          | ~ (v1_relat_1 @ X25)
% 1.45/1.64          | ~ (r2_hidden @ X24 @ X25))),
% 1.45/1.64      inference('cnf', [status(esa)], [t23_mcart_1])).
% 1.45/1.64  thf('10', plain,
% 1.45/1.64      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.45/1.64        | ~ (v1_relat_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.45/1.64        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 1.45/1.64      inference('sup-', [status(thm)], ['8', '9'])).
% 1.45/1.64  thf(d3_zfmisc_1, axiom,
% 1.45/1.64    (![A:$i,B:$i,C:$i]:
% 1.45/1.64     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 1.45/1.64       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 1.45/1.64  thf('11', plain,
% 1.45/1.64      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.45/1.64         ((k3_zfmisc_1 @ X14 @ X15 @ X16)
% 1.45/1.64           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15) @ X16))),
% 1.45/1.64      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.45/1.64  thf(fc6_relat_1, axiom,
% 1.45/1.64    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.45/1.64  thf('12', plain,
% 1.45/1.64      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 1.45/1.64      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.45/1.64  thf('13', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.45/1.64         (v1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))),
% 1.45/1.64      inference('sup+', [status(thm)], ['11', '12'])).
% 1.45/1.64  thf('14', plain,
% 1.45/1.64      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.45/1.64        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 1.45/1.64      inference('demod', [status(thm)], ['10', '13'])).
% 1.45/1.64  thf('15', plain,
% 1.45/1.64      (![X35 : $i]:
% 1.45/1.64         (((X35) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X35) @ X35))),
% 1.45/1.64      inference('cnf', [status(esa)], [t6_mcart_1])).
% 1.45/1.64  thf('16', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.45/1.64      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.45/1.64  thf('17', plain,
% 1.45/1.64      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.45/1.64      inference('sup-', [status(thm)], ['15', '16'])).
% 1.45/1.64  thf('18', plain,
% 1.45/1.64      ((((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 1.45/1.64        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 1.45/1.64      inference('sup-', [status(thm)], ['14', '17'])).
% 1.45/1.64  thf(d4_zfmisc_1, axiom,
% 1.45/1.64    (![A:$i,B:$i,C:$i,D:$i]:
% 1.45/1.64     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 1.45/1.64       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 1.45/1.64  thf('19', plain,
% 1.45/1.64      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.45/1.64         ((k4_zfmisc_1 @ X17 @ X18 @ X19 @ X20)
% 1.45/1.64           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X17 @ X18 @ X19) @ X20))),
% 1.45/1.64      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.45/1.64  thf('20', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0)
% 1.45/1.64            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 1.45/1.64          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 1.45/1.64      inference('sup+', [status(thm)], ['18', '19'])).
% 1.45/1.64  thf(t55_mcart_1, axiom,
% 1.45/1.64    (![A:$i,B:$i,C:$i,D:$i]:
% 1.45/1.64     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.45/1.64         ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) ) <=>
% 1.45/1.64       ( ( k4_zfmisc_1 @ A @ B @ C @ D ) != ( k1_xboole_0 ) ) ))).
% 1.45/1.64  thf('21', plain,
% 1.45/1.64      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.45/1.64         (((k4_zfmisc_1 @ X30 @ X31 @ X32 @ X33) != (k1_xboole_0))
% 1.45/1.64          | ((X33) = (k1_xboole_0))
% 1.45/1.64          | ((X32) = (k1_xboole_0))
% 1.45/1.64          | ((X31) = (k1_xboole_0))
% 1.45/1.64          | ((X30) = (k1_xboole_0)))),
% 1.45/1.64      inference('cnf', [status(esa)], [t55_mcart_1])).
% 1.45/1.64  thf('22', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         (((k2_zfmisc_1 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 1.45/1.64          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 1.45/1.64          | ((sk_A) = (k1_xboole_0))
% 1.45/1.64          | ((sk_B_2) = (k1_xboole_0))
% 1.45/1.64          | ((sk_C) = (k1_xboole_0))
% 1.45/1.64          | ((X0) = (k1_xboole_0)))),
% 1.45/1.64      inference('sup-', [status(thm)], ['20', '21'])).
% 1.45/1.64  thf('23', plain, (((sk_C) != (k1_xboole_0))),
% 1.45/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.64  thf('24', plain, (((sk_B_2) != (k1_xboole_0))),
% 1.45/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.64  thf('25', plain, (((sk_A) != (k1_xboole_0))),
% 1.45/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.64  thf('26', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         (((k2_zfmisc_1 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 1.45/1.64          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 1.45/1.64          | ((X0) = (k1_xboole_0)))),
% 1.45/1.64      inference('simplify_reflect-', [status(thm)], ['22', '23', '24', '25'])).
% 1.45/1.64  thf('27', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         (((k1_xboole_0) != (k1_xboole_0))
% 1.45/1.64          | ~ (v1_xboole_0 @ k1_xboole_0)
% 1.45/1.64          | ((X0) = (k1_xboole_0))
% 1.45/1.64          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 1.45/1.64      inference('sup-', [status(thm)], ['5', '26'])).
% 1.45/1.64  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.45/1.64  thf('28', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.45/1.64      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.45/1.64  thf('29', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         (((k1_xboole_0) != (k1_xboole_0))
% 1.45/1.64          | ((X0) = (k1_xboole_0))
% 1.45/1.64          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 1.45/1.64      inference('demod', [status(thm)], ['27', '28'])).
% 1.45/1.64  thf('30', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         (((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 1.45/1.64          | ((X0) = (k1_xboole_0)))),
% 1.45/1.64      inference('simplify', [status(thm)], ['29'])).
% 1.45/1.64  thf('31', plain,
% 1.45/1.64      ((((k1_xboole_0) != (sk_E))
% 1.45/1.64        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 1.45/1.64      inference('eq_fact', [status(thm)], ['30'])).
% 1.45/1.64  thf('32', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         (((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 1.45/1.64          | ((X0) = (k1_xboole_0)))),
% 1.45/1.64      inference('simplify', [status(thm)], ['29'])).
% 1.45/1.64  thf('33', plain,
% 1.45/1.64      (((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))),
% 1.45/1.64      inference('clc', [status(thm)], ['31', '32'])).
% 1.45/1.64  thf('34', plain,
% 1.45/1.64      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.45/1.64        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 1.45/1.64      inference('sup-', [status(thm)], ['6', '7'])).
% 1.45/1.64  thf('35', plain,
% 1.45/1.64      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.45/1.64         ((k3_zfmisc_1 @ X14 @ X15 @ X16)
% 1.45/1.64           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15) @ X16))),
% 1.45/1.64      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.45/1.64  thf('36', plain,
% 1.45/1.64      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.45/1.64         ((r2_hidden @ (k1_mcart_1 @ X21) @ X22)
% 1.45/1.64          | ~ (r2_hidden @ X21 @ (k2_zfmisc_1 @ X22 @ X23)))),
% 1.45/1.64      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.45/1.64  thf('37', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.45/1.64         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.45/1.64          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 1.45/1.64      inference('sup-', [status(thm)], ['35', '36'])).
% 1.45/1.64  thf('38', plain,
% 1.45/1.64      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.45/1.64        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.45/1.64      inference('sup-', [status(thm)], ['34', '37'])).
% 1.45/1.64  thf('39', plain,
% 1.45/1.64      (![X24 : $i, X25 : $i]:
% 1.45/1.64         (((X24) = (k4_tarski @ (k1_mcart_1 @ X24) @ (k2_mcart_1 @ X24)))
% 1.45/1.64          | ~ (v1_relat_1 @ X25)
% 1.45/1.64          | ~ (r2_hidden @ X24 @ X25))),
% 1.45/1.64      inference('cnf', [status(esa)], [t23_mcart_1])).
% 1.45/1.64  thf('40', plain,
% 1.45/1.64      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.45/1.64        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))
% 1.45/1.64        | ((k1_mcart_1 @ sk_E)
% 1.45/1.64            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 1.45/1.64               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 1.45/1.64      inference('sup-', [status(thm)], ['38', '39'])).
% 1.45/1.64  thf('41', plain,
% 1.45/1.64      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 1.45/1.64      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.45/1.64  thf('42', plain,
% 1.45/1.64      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.45/1.64        | ((k1_mcart_1 @ sk_E)
% 1.45/1.64            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 1.45/1.64               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 1.45/1.64      inference('demod', [status(thm)], ['40', '41'])).
% 1.45/1.64  thf('43', plain,
% 1.45/1.64      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.45/1.64      inference('sup-', [status(thm)], ['15', '16'])).
% 1.45/1.64  thf('44', plain,
% 1.45/1.64      ((((k1_mcart_1 @ sk_E)
% 1.45/1.64          = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 1.45/1.64             (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 1.45/1.64        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 1.45/1.64      inference('sup-', [status(thm)], ['42', '43'])).
% 1.45/1.64  thf(d3_mcart_1, axiom,
% 1.45/1.64    (![A:$i,B:$i,C:$i]:
% 1.45/1.64     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 1.45/1.64  thf('45', plain,
% 1.45/1.64      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.45/1.64         ((k3_mcart_1 @ X11 @ X12 @ X13)
% 1.45/1.64           = (k4_tarski @ (k4_tarski @ X11 @ X12) @ X13))),
% 1.45/1.64      inference('cnf', [status(esa)], [d3_mcart_1])).
% 1.45/1.64  thf('46', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         (((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 1.45/1.64            (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X0)
% 1.45/1.64            = (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 1.45/1.64          | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 1.45/1.64      inference('sup+', [status(thm)], ['44', '45'])).
% 1.45/1.64  thf('47', plain,
% 1.45/1.64      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.45/1.64        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.45/1.64      inference('sup-', [status(thm)], ['34', '37'])).
% 1.45/1.64  thf('48', plain,
% 1.45/1.64      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.45/1.64         ((r2_hidden @ (k2_mcart_1 @ X21) @ X23)
% 1.45/1.64          | ~ (r2_hidden @ X21 @ (k2_zfmisc_1 @ X22 @ X23)))),
% 1.45/1.64      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.45/1.64  thf('49', plain,
% 1.45/1.64      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.45/1.64        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2))),
% 1.45/1.64      inference('sup-', [status(thm)], ['47', '48'])).
% 1.45/1.64  thf('50', plain,
% 1.45/1.64      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.45/1.64      inference('sup-', [status(thm)], ['15', '16'])).
% 1.45/1.64  thf('51', plain,
% 1.45/1.64      (((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2)
% 1.45/1.64        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 1.45/1.64      inference('sup-', [status(thm)], ['49', '50'])).
% 1.45/1.64  thf('52', plain,
% 1.45/1.64      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.45/1.64         ((k4_zfmisc_1 @ X17 @ X18 @ X19 @ X20)
% 1.45/1.64           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X17 @ X18 @ X19) @ X20))),
% 1.45/1.64      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.45/1.64  thf('53', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0)
% 1.45/1.64            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 1.45/1.64          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2))),
% 1.45/1.64      inference('sup+', [status(thm)], ['51', '52'])).
% 1.45/1.64  thf('54', plain,
% 1.45/1.64      (![X30 : $i, X31 : $i, X32 : $i, X34 : $i]:
% 1.45/1.64         (((X32) != (k1_xboole_0))
% 1.45/1.64          | ((k4_zfmisc_1 @ X30 @ X31 @ X32 @ X34) = (k1_xboole_0)))),
% 1.45/1.64      inference('cnf', [status(esa)], [t55_mcart_1])).
% 1.45/1.64  thf('55', plain,
% 1.45/1.64      (![X30 : $i, X31 : $i, X34 : $i]:
% 1.45/1.64         ((k4_zfmisc_1 @ X30 @ X31 @ k1_xboole_0 @ X34) = (k1_xboole_0))),
% 1.45/1.64      inference('simplify', [status(thm)], ['54'])).
% 1.45/1.64  thf('56', plain,
% 1.45/1.64      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.45/1.64         ((k3_zfmisc_1 @ X14 @ X15 @ X16)
% 1.45/1.64           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15) @ X16))),
% 1.45/1.64      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.45/1.64  thf('57', plain,
% 1.45/1.64      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.45/1.64         ((k3_zfmisc_1 @ X14 @ X15 @ X16)
% 1.45/1.64           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15) @ X16))),
% 1.45/1.64      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.45/1.64  thf('58', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.45/1.64         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 1.45/1.64           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 1.45/1.64      inference('sup+', [status(thm)], ['56', '57'])).
% 1.45/1.64  thf('59', plain,
% 1.45/1.64      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.45/1.64         ((k4_zfmisc_1 @ X17 @ X18 @ X19 @ X20)
% 1.45/1.64           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X17 @ X18 @ X19) @ X20))),
% 1.45/1.64      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.45/1.64  thf('60', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.45/1.64         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 1.45/1.64           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 1.45/1.64      inference('demod', [status(thm)], ['58', '59'])).
% 1.45/1.64  thf('61', plain,
% 1.45/1.64      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.45/1.64         ((k4_zfmisc_1 @ X17 @ X18 @ X19 @ X20)
% 1.45/1.64           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X17 @ X18 @ X19) @ X20))),
% 1.45/1.64      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.45/1.64  thf('62', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.45/1.64         ((k4_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0 @ X4)
% 1.45/1.64           = (k2_zfmisc_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) @ X4))),
% 1.45/1.64      inference('sup+', [status(thm)], ['60', '61'])).
% 1.45/1.64  thf('63', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.45/1.64         ((k1_xboole_0)
% 1.45/1.64           = (k2_zfmisc_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ k1_xboole_0) @ X0))),
% 1.45/1.64      inference('sup+', [status(thm)], ['55', '62'])).
% 1.45/1.64  thf('64', plain,
% 1.45/1.64      (![X30 : $i, X31 : $i, X32 : $i, X34 : $i]:
% 1.45/1.64         (((X34) != (k1_xboole_0))
% 1.45/1.64          | ((k4_zfmisc_1 @ X30 @ X31 @ X32 @ X34) = (k1_xboole_0)))),
% 1.45/1.64      inference('cnf', [status(esa)], [t55_mcart_1])).
% 1.45/1.64  thf('65', plain,
% 1.45/1.64      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.45/1.64         ((k4_zfmisc_1 @ X30 @ X31 @ X32 @ k1_xboole_0) = (k1_xboole_0))),
% 1.45/1.64      inference('simplify', [status(thm)], ['64'])).
% 1.45/1.64  thf('66', plain,
% 1.45/1.64      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 1.45/1.64      inference('demod', [status(thm)], ['63', '65'])).
% 1.45/1.64  thf('67', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0) = (k1_xboole_0))
% 1.45/1.64          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2))),
% 1.45/1.64      inference('demod', [status(thm)], ['53', '66'])).
% 1.45/1.64  thf('68', plain,
% 1.45/1.64      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.45/1.64         (((k4_zfmisc_1 @ X30 @ X31 @ X32 @ X33) != (k1_xboole_0))
% 1.45/1.64          | ((X33) = (k1_xboole_0))
% 1.45/1.64          | ((X32) = (k1_xboole_0))
% 1.45/1.64          | ((X31) = (k1_xboole_0))
% 1.45/1.64          | ((X30) = (k1_xboole_0)))),
% 1.45/1.64      inference('cnf', [status(esa)], [t55_mcart_1])).
% 1.45/1.64  thf('69', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         (((k1_xboole_0) != (k1_xboole_0))
% 1.45/1.64          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2)
% 1.45/1.64          | ((sk_A) = (k1_xboole_0))
% 1.45/1.64          | ((sk_B_2) = (k1_xboole_0))
% 1.45/1.64          | ((sk_C) = (k1_xboole_0))
% 1.45/1.64          | ((X0) = (k1_xboole_0)))),
% 1.45/1.64      inference('sup-', [status(thm)], ['67', '68'])).
% 1.45/1.64  thf('70', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         (((X0) = (k1_xboole_0))
% 1.45/1.64          | ((sk_C) = (k1_xboole_0))
% 1.45/1.64          | ((sk_B_2) = (k1_xboole_0))
% 1.45/1.64          | ((sk_A) = (k1_xboole_0))
% 1.45/1.64          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2))),
% 1.45/1.64      inference('simplify', [status(thm)], ['69'])).
% 1.45/1.64  thf('71', plain, (((sk_A) != (k1_xboole_0))),
% 1.45/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.64  thf('72', plain, (((sk_B_2) != (k1_xboole_0))),
% 1.45/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.64  thf('73', plain, (((sk_C) != (k1_xboole_0))),
% 1.45/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.64  thf('74', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         (((X0) = (k1_xboole_0))
% 1.45/1.64          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2))),
% 1.45/1.64      inference('simplify_reflect-', [status(thm)], ['70', '71', '72', '73'])).
% 1.45/1.64  thf(t1_subset, axiom,
% 1.45/1.64    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 1.45/1.64  thf('75', plain,
% 1.45/1.64      (![X5 : $i, X6 : $i]: ((m1_subset_1 @ X5 @ X6) | ~ (r2_hidden @ X5 @ X6))),
% 1.45/1.64      inference('cnf', [status(esa)], [t1_subset])).
% 1.45/1.64  thf('76', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         (((X0) = (k1_xboole_0))
% 1.45/1.64          | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2))),
% 1.45/1.64      inference('sup-', [status(thm)], ['74', '75'])).
% 1.45/1.64  thf('77', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.45/1.64      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.45/1.64  thf('78', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         ((v1_xboole_0 @ X0)
% 1.45/1.64          | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2))),
% 1.45/1.64      inference('sup+', [status(thm)], ['76', '77'])).
% 1.45/1.64  thf(fc1_zfmisc_1, axiom,
% 1.45/1.64    (![A:$i,B:$i]: ( ~( v1_xboole_0 @ ( k4_tarski @ A @ B ) ) ))).
% 1.45/1.64  thf('79', plain,
% 1.45/1.64      (![X3 : $i, X4 : $i]: ~ (v1_xboole_0 @ (k4_tarski @ X3 @ X4))),
% 1.45/1.64      inference('cnf', [status(esa)], [fc1_zfmisc_1])).
% 1.45/1.64  thf('80', plain,
% 1.45/1.64      ((m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2)),
% 1.45/1.64      inference('sup-', [status(thm)], ['78', '79'])).
% 1.45/1.64  thf('81', plain,
% 1.45/1.64      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.45/1.64         (~ (m1_subset_1 @ X41 @ sk_B_2)
% 1.45/1.64          | ((sk_E) != (k3_mcart_1 @ X42 @ X41 @ X43))
% 1.45/1.64          | ((sk_D) = (X43))
% 1.45/1.64          | ~ (m1_subset_1 @ X43 @ sk_C)
% 1.45/1.64          | ~ (m1_subset_1 @ X42 @ sk_A))),
% 1.45/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.64  thf('82', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         (~ (m1_subset_1 @ X0 @ sk_A)
% 1.45/1.64          | ~ (m1_subset_1 @ X1 @ sk_C)
% 1.45/1.64          | ((sk_D) = (X1))
% 1.45/1.64          | ((sk_E)
% 1.45/1.64              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1)))),
% 1.45/1.64      inference('sup-', [status(thm)], ['80', '81'])).
% 1.45/1.64  thf('83', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 1.45/1.64          | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0))
% 1.45/1.64          | ((sk_D) = (X0))
% 1.45/1.64          | ~ (m1_subset_1 @ X0 @ sk_C)
% 1.45/1.64          | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 1.45/1.64      inference('sup-', [status(thm)], ['46', '82'])).
% 1.45/1.64  thf('84', plain,
% 1.45/1.64      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.45/1.64        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.45/1.64      inference('sup-', [status(thm)], ['34', '37'])).
% 1.45/1.64  thf('85', plain,
% 1.45/1.64      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.45/1.64         ((r2_hidden @ (k1_mcart_1 @ X21) @ X22)
% 1.45/1.64          | ~ (r2_hidden @ X21 @ (k2_zfmisc_1 @ X22 @ X23)))),
% 1.45/1.64      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.45/1.64  thf('86', plain,
% 1.45/1.64      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.45/1.64        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 1.45/1.64      inference('sup-', [status(thm)], ['84', '85'])).
% 1.45/1.64  thf('87', plain,
% 1.45/1.64      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.45/1.64      inference('sup-', [status(thm)], ['15', '16'])).
% 1.45/1.64  thf('88', plain,
% 1.45/1.64      (((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 1.45/1.64        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 1.45/1.64      inference('sup-', [status(thm)], ['86', '87'])).
% 1.45/1.64  thf('89', plain,
% 1.45/1.64      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.45/1.64         ((k4_zfmisc_1 @ X17 @ X18 @ X19 @ X20)
% 1.45/1.64           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X17 @ X18 @ X19) @ X20))),
% 1.45/1.64      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.45/1.64  thf('90', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0)
% 1.45/1.64            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 1.45/1.64          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 1.45/1.64      inference('sup+', [status(thm)], ['88', '89'])).
% 1.45/1.64  thf('91', plain,
% 1.45/1.64      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 1.45/1.64      inference('demod', [status(thm)], ['63', '65'])).
% 1.45/1.64  thf('92', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0) = (k1_xboole_0))
% 1.45/1.64          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 1.45/1.64      inference('demod', [status(thm)], ['90', '91'])).
% 1.45/1.64  thf('93', plain,
% 1.45/1.64      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.45/1.64         (((k4_zfmisc_1 @ X30 @ X31 @ X32 @ X33) != (k1_xboole_0))
% 1.45/1.64          | ((X33) = (k1_xboole_0))
% 1.45/1.64          | ((X32) = (k1_xboole_0))
% 1.45/1.64          | ((X31) = (k1_xboole_0))
% 1.45/1.64          | ((X30) = (k1_xboole_0)))),
% 1.45/1.64      inference('cnf', [status(esa)], [t55_mcart_1])).
% 1.45/1.64  thf('94', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         (((k1_xboole_0) != (k1_xboole_0))
% 1.45/1.64          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 1.45/1.64          | ((sk_A) = (k1_xboole_0))
% 1.45/1.64          | ((sk_B_2) = (k1_xboole_0))
% 1.45/1.64          | ((sk_C) = (k1_xboole_0))
% 1.45/1.64          | ((X0) = (k1_xboole_0)))),
% 1.45/1.64      inference('sup-', [status(thm)], ['92', '93'])).
% 1.45/1.64  thf('95', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         (((X0) = (k1_xboole_0))
% 1.45/1.64          | ((sk_C) = (k1_xboole_0))
% 1.45/1.64          | ((sk_B_2) = (k1_xboole_0))
% 1.45/1.64          | ((sk_A) = (k1_xboole_0))
% 1.45/1.64          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 1.45/1.64      inference('simplify', [status(thm)], ['94'])).
% 1.45/1.64  thf('96', plain, (((sk_A) != (k1_xboole_0))),
% 1.45/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.64  thf('97', plain, (((sk_B_2) != (k1_xboole_0))),
% 1.45/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.64  thf('98', plain, (((sk_C) != (k1_xboole_0))),
% 1.45/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.64  thf('99', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         (((X0) = (k1_xboole_0))
% 1.45/1.64          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 1.45/1.64      inference('simplify_reflect-', [status(thm)], ['95', '96', '97', '98'])).
% 1.45/1.64  thf('100', plain,
% 1.45/1.64      (![X5 : $i, X6 : $i]: ((m1_subset_1 @ X5 @ X6) | ~ (r2_hidden @ X5 @ X6))),
% 1.45/1.64      inference('cnf', [status(esa)], [t1_subset])).
% 1.45/1.64  thf('101', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         (((X0) = (k1_xboole_0))
% 1.45/1.64          | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 1.45/1.64      inference('sup-', [status(thm)], ['99', '100'])).
% 1.45/1.64  thf('102', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.45/1.64      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.45/1.64  thf('103', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         ((v1_xboole_0 @ X0)
% 1.45/1.64          | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 1.45/1.64      inference('sup+', [status(thm)], ['101', '102'])).
% 1.45/1.64  thf('104', plain,
% 1.45/1.64      (![X3 : $i, X4 : $i]: ~ (v1_xboole_0 @ (k4_tarski @ X3 @ X4))),
% 1.45/1.64      inference('cnf', [status(esa)], [fc1_zfmisc_1])).
% 1.45/1.64  thf('105', plain,
% 1.45/1.64      ((m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)),
% 1.45/1.64      inference('sup-', [status(thm)], ['103', '104'])).
% 1.45/1.64  thf('106', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 1.45/1.64          | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0))
% 1.45/1.64          | ((sk_D) = (X0))
% 1.45/1.64          | ~ (m1_subset_1 @ X0 @ sk_C))),
% 1.45/1.64      inference('demod', [status(thm)], ['83', '105'])).
% 1.45/1.64  thf('107', plain,
% 1.45/1.64      ((((sk_E) != (sk_E))
% 1.45/1.64        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)
% 1.45/1.64        | ((sk_D) = (k2_mcart_1 @ sk_E))
% 1.45/1.64        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 1.45/1.64      inference('sup-', [status(thm)], ['33', '106'])).
% 1.45/1.64  thf('108', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i]:
% 1.45/1.64         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.45/1.64      inference('sup-', [status(thm)], ['3', '4'])).
% 1.45/1.64  thf('109', plain,
% 1.45/1.64      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.45/1.64        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 1.45/1.64      inference('sup-', [status(thm)], ['6', '7'])).
% 1.45/1.64  thf('110', plain,
% 1.45/1.64      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.45/1.64         ((k3_zfmisc_1 @ X14 @ X15 @ X16)
% 1.45/1.64           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15) @ X16))),
% 1.45/1.64      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.45/1.64  thf('111', plain,
% 1.45/1.64      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.45/1.64         ((r2_hidden @ (k2_mcart_1 @ X21) @ X23)
% 1.45/1.64          | ~ (r2_hidden @ X21 @ (k2_zfmisc_1 @ X22 @ X23)))),
% 1.45/1.64      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.45/1.64  thf('112', plain,
% 1.45/1.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.45/1.64         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.45/1.64          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 1.45/1.64      inference('sup-', [status(thm)], ['110', '111'])).
% 1.45/1.64  thf('113', plain,
% 1.45/1.64      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.45/1.64        | (r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C))),
% 1.45/1.64      inference('sup-', [status(thm)], ['109', '112'])).
% 1.45/1.64  thf('114', plain,
% 1.45/1.64      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.45/1.64      inference('sup-', [status(thm)], ['15', '16'])).
% 1.45/1.64  thf('115', plain,
% 1.45/1.64      (((r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C)
% 1.45/1.64        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 1.45/1.64      inference('sup-', [status(thm)], ['113', '114'])).
% 1.45/1.64  thf('116', plain,
% 1.45/1.64      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.45/1.64         ((k4_zfmisc_1 @ X17 @ X18 @ X19 @ X20)
% 1.45/1.64           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X17 @ X18 @ X19) @ X20))),
% 1.45/1.64      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.45/1.64  thf('117', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0)
% 1.45/1.64            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 1.45/1.64          | (r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C))),
% 1.45/1.64      inference('sup+', [status(thm)], ['115', '116'])).
% 1.45/1.64  thf('118', plain,
% 1.45/1.64      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.45/1.64         (((k4_zfmisc_1 @ X30 @ X31 @ X32 @ X33) != (k1_xboole_0))
% 1.45/1.64          | ((X33) = (k1_xboole_0))
% 1.45/1.64          | ((X32) = (k1_xboole_0))
% 1.45/1.64          | ((X31) = (k1_xboole_0))
% 1.45/1.64          | ((X30) = (k1_xboole_0)))),
% 1.45/1.64      inference('cnf', [status(esa)], [t55_mcart_1])).
% 1.45/1.64  thf('119', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         (((k2_zfmisc_1 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 1.45/1.64          | (r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C)
% 1.45/1.64          | ((sk_A) = (k1_xboole_0))
% 1.45/1.64          | ((sk_B_2) = (k1_xboole_0))
% 1.45/1.64          | ((sk_C) = (k1_xboole_0))
% 1.45/1.64          | ((X0) = (k1_xboole_0)))),
% 1.45/1.64      inference('sup-', [status(thm)], ['117', '118'])).
% 1.45/1.64  thf('120', plain, (((sk_C) != (k1_xboole_0))),
% 1.45/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.64  thf('121', plain, (((sk_B_2) != (k1_xboole_0))),
% 1.45/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.64  thf('122', plain, (((sk_A) != (k1_xboole_0))),
% 1.45/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.64  thf('123', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         (((k2_zfmisc_1 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 1.45/1.64          | (r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C)
% 1.45/1.64          | ((X0) = (k1_xboole_0)))),
% 1.45/1.64      inference('simplify_reflect-', [status(thm)],
% 1.45/1.64                ['119', '120', '121', '122'])).
% 1.45/1.64  thf('124', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         (((k1_xboole_0) != (k1_xboole_0))
% 1.45/1.64          | ~ (v1_xboole_0 @ k1_xboole_0)
% 1.45/1.64          | ((X0) = (k1_xboole_0))
% 1.45/1.64          | (r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C))),
% 1.45/1.64      inference('sup-', [status(thm)], ['108', '123'])).
% 1.45/1.64  thf('125', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.45/1.64      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.45/1.64  thf('126', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         (((k1_xboole_0) != (k1_xboole_0))
% 1.45/1.64          | ((X0) = (k1_xboole_0))
% 1.45/1.64          | (r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C))),
% 1.45/1.64      inference('demod', [status(thm)], ['124', '125'])).
% 1.45/1.64  thf('127', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         ((r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C) | ((X0) = (k1_xboole_0)))),
% 1.45/1.64      inference('simplify', [status(thm)], ['126'])).
% 1.45/1.64  thf('128', plain,
% 1.45/1.64      (![X5 : $i, X6 : $i]: ((m1_subset_1 @ X5 @ X6) | ~ (r2_hidden @ X5 @ X6))),
% 1.45/1.64      inference('cnf', [status(esa)], [t1_subset])).
% 1.45/1.64  thf('129', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         (((X0) = (k1_xboole_0)) | (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C))),
% 1.45/1.64      inference('sup-', [status(thm)], ['127', '128'])).
% 1.45/1.64  thf('130', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.45/1.64      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.45/1.64  thf('131', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         ((v1_xboole_0 @ X0) | (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C))),
% 1.45/1.64      inference('sup+', [status(thm)], ['129', '130'])).
% 1.45/1.64  thf('132', plain,
% 1.45/1.64      (![X3 : $i, X4 : $i]: ~ (v1_xboole_0 @ (k4_tarski @ X3 @ X4))),
% 1.45/1.64      inference('cnf', [status(esa)], [fc1_zfmisc_1])).
% 1.45/1.64  thf('133', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)),
% 1.45/1.64      inference('sup-', [status(thm)], ['131', '132'])).
% 1.45/1.64  thf('134', plain,
% 1.45/1.64      ((((sk_E) != (sk_E))
% 1.45/1.64        | ((sk_D) = (k2_mcart_1 @ sk_E))
% 1.45/1.64        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 1.45/1.64      inference('demod', [status(thm)], ['107', '133'])).
% 1.45/1.64  thf('135', plain,
% 1.45/1.64      ((((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0))
% 1.45/1.64        | ((sk_D) = (k2_mcart_1 @ sk_E)))),
% 1.45/1.64      inference('simplify', [status(thm)], ['134'])).
% 1.45/1.64  thf('136', plain, (((sk_D) != (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E))),
% 1.45/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.64  thf('137', plain,
% 1.45/1.64      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 1.45/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.64  thf(t50_mcart_1, axiom,
% 1.45/1.64    (![A:$i,B:$i,C:$i]:
% 1.45/1.64     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.45/1.64          ( ( C ) != ( k1_xboole_0 ) ) & 
% 1.45/1.64          ( ~( ![D:$i]:
% 1.45/1.64               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.45/1.64                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 1.45/1.64                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 1.45/1.64                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 1.45/1.64                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 1.45/1.64                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 1.45/1.64  thf('138', plain,
% 1.45/1.64      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.45/1.64         (((X26) = (k1_xboole_0))
% 1.45/1.64          | ((X27) = (k1_xboole_0))
% 1.45/1.64          | ((k7_mcart_1 @ X26 @ X27 @ X29 @ X28) = (k2_mcart_1 @ X28))
% 1.45/1.64          | ~ (m1_subset_1 @ X28 @ (k3_zfmisc_1 @ X26 @ X27 @ X29))
% 1.45/1.64          | ((X29) = (k1_xboole_0)))),
% 1.45/1.64      inference('cnf', [status(esa)], [t50_mcart_1])).
% 1.45/1.64  thf('139', plain,
% 1.45/1.64      ((((sk_C) = (k1_xboole_0))
% 1.45/1.64        | ((k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))
% 1.45/1.64        | ((sk_B_2) = (k1_xboole_0))
% 1.45/1.64        | ((sk_A) = (k1_xboole_0)))),
% 1.45/1.64      inference('sup-', [status(thm)], ['137', '138'])).
% 1.45/1.64  thf('140', plain, (((sk_A) != (k1_xboole_0))),
% 1.45/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.64  thf('141', plain, (((sk_B_2) != (k1_xboole_0))),
% 1.45/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.64  thf('142', plain, (((sk_C) != (k1_xboole_0))),
% 1.45/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.64  thf('143', plain,
% 1.45/1.64      (((k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))),
% 1.45/1.64      inference('simplify_reflect-', [status(thm)],
% 1.45/1.64                ['139', '140', '141', '142'])).
% 1.45/1.64  thf('144', plain, (((sk_D) != (k2_mcart_1 @ sk_E))),
% 1.45/1.64      inference('demod', [status(thm)], ['136', '143'])).
% 1.45/1.64  thf('145', plain, (((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0))),
% 1.45/1.64      inference('simplify_reflect-', [status(thm)], ['135', '144'])).
% 1.45/1.64  thf('146', plain,
% 1.45/1.64      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.45/1.64         ((k4_zfmisc_1 @ X17 @ X18 @ X19 @ X20)
% 1.45/1.64           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X17 @ X18 @ X19) @ X20))),
% 1.45/1.64      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.45/1.64  thf('147', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         ((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0)
% 1.45/1.64           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 1.45/1.64      inference('sup+', [status(thm)], ['145', '146'])).
% 1.45/1.64  thf('148', plain,
% 1.45/1.64      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 1.45/1.64      inference('demod', [status(thm)], ['63', '65'])).
% 1.45/1.64  thf('149', plain,
% 1.45/1.64      (![X0 : $i]: ((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0) = (k1_xboole_0))),
% 1.45/1.64      inference('demod', [status(thm)], ['147', '148'])).
% 1.45/1.64  thf('150', plain,
% 1.45/1.64      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.45/1.64         (((k4_zfmisc_1 @ X30 @ X31 @ X32 @ X33) != (k1_xboole_0))
% 1.45/1.64          | ((X33) = (k1_xboole_0))
% 1.45/1.64          | ((X32) = (k1_xboole_0))
% 1.45/1.64          | ((X31) = (k1_xboole_0))
% 1.45/1.64          | ((X30) = (k1_xboole_0)))),
% 1.45/1.64      inference('cnf', [status(esa)], [t55_mcart_1])).
% 1.45/1.64  thf('151', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         (((k1_xboole_0) != (k1_xboole_0))
% 1.45/1.64          | ((sk_A) = (k1_xboole_0))
% 1.45/1.64          | ((sk_B_2) = (k1_xboole_0))
% 1.45/1.64          | ((sk_C) = (k1_xboole_0))
% 1.45/1.64          | ((X0) = (k1_xboole_0)))),
% 1.45/1.64      inference('sup-', [status(thm)], ['149', '150'])).
% 1.45/1.64  thf('152', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         (((X0) = (k1_xboole_0))
% 1.45/1.64          | ((sk_C) = (k1_xboole_0))
% 1.45/1.64          | ((sk_B_2) = (k1_xboole_0))
% 1.45/1.64          | ((sk_A) = (k1_xboole_0)))),
% 1.45/1.64      inference('simplify', [status(thm)], ['151'])).
% 1.45/1.64  thf('153', plain, (((sk_A) != (k1_xboole_0))),
% 1.45/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.64  thf('154', plain, (((sk_B_2) != (k1_xboole_0))),
% 1.45/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.64  thf('155', plain, (((sk_C) != (k1_xboole_0))),
% 1.45/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.64  thf('156', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 1.45/1.64      inference('simplify_reflect-', [status(thm)],
% 1.45/1.64                ['152', '153', '154', '155'])).
% 1.45/1.64  thf('157', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 1.45/1.64      inference('demod', [status(thm)], ['0', '156'])).
% 1.45/1.64  thf('158', plain, ($false), inference('simplify', [status(thm)], ['157'])).
% 1.45/1.64  
% 1.45/1.64  % SZS output end Refutation
% 1.45/1.64  
% 1.45/1.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
