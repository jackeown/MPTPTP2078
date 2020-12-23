%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.j4oCrlRitV

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:56 EST 2020

% Result     : Theorem 0.82s
% Output     : Refutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :  165 (1132 expanded)
%              Number of leaves         :   43 ( 363 expanded)
%              Depth                    :   27
%              Number of atoms          : 1311 (16680 expanded)
%              Number of equality atoms :  157 (2112 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

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
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1 ) )
    | ( r2_hidden @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13
        = ( k4_tarski @ ( sk_C @ X13 ) @ ( sk_D_1 @ X13 ) ) )
      | ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1 ) )
    | ( sk_E_1
      = ( k4_tarski @ ( sk_C @ sk_E_1 ) @ ( sk_D_1 @ sk_E_1 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k3_zfmisc_1 @ X23 @ X24 @ X25 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( v1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1 ) )
    | ( sk_E_1
      = ( k4_tarski @ ( sk_C @ sk_E_1 ) @ ( sk_D_1 @ sk_E_1 ) ) ) ),
    inference(demod,[status(thm)],['4','7'])).

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

thf('9',plain,(
    ! [X33: $i] :
      ( ( X33 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_2 @ X33 ) @ X33 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('10',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X30 ) @ X31 )
      | ~ ( r2_hidden @ X30 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( sk_B_2 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( sk_E_1
        = ( k4_tarski @ ( sk_C @ sk_E_1 ) @ ( sk_D_1 @ sk_E_1 ) ) )
      | ( ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('15',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k4_zfmisc_1 @ X26 @ X27 @ X28 @ X29 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X26 @ X27 @ X28 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( sk_E_1
        = ( k4_tarski @ ( sk_C @ sk_E_1 ) @ ( sk_D_1 @ sk_E_1 ) ) )
      | ( ( k4_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t55_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 ) )
    <=> ( ( k4_zfmisc_1 @ A @ B @ C @ D )
       != k1_xboole_0 ) ) )).

thf('17',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( ( k4_zfmisc_1 @ X42 @ X43 @ X44 @ X45 )
       != k1_xboole_0 )
      | ( X45 = k1_xboole_0 )
      | ( X44 = k1_xboole_0 )
      | ( X43 = k1_xboole_0 )
      | ( X42 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_E_1
        = ( k4_tarski @ ( sk_C @ sk_E_1 ) @ ( sk_D_1 @ sk_E_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_3 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( sk_B_3 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_E_1
        = ( k4_tarski @ ( sk_C @ sk_E_1 ) @ ( sk_D_1 @ sk_E_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    sk_B_3 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_E_1
        = ( k4_tarski @ ( sk_C @ sk_E_1 ) @ ( sk_D_1 @ sk_E_1 ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['19','20','21','22'])).

thf('24',plain,
    ( ( k1_xboole_0 != sk_E_1 )
    | ( sk_E_1
      = ( k4_tarski @ ( sk_C @ sk_E_1 ) @ ( sk_D_1 @ sk_E_1 ) ) ) ),
    inference(eq_fact,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_E_1
        = ( k4_tarski @ ( sk_C @ sk_E_1 ) @ ( sk_D_1 @ sk_E_1 ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['19','20','21','22'])).

thf('26',plain,
    ( sk_E_1
    = ( k4_tarski @ ( sk_C @ sk_E_1 ) @ ( sk_D_1 @ sk_E_1 ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,
    ( sk_E_1
    = ( k4_tarski @ ( sk_C @ sk_E_1 ) @ ( sk_D_1 @ sk_E_1 ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('28',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X47 @ X48 ) )
      = X47 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('29',plain,
    ( ( k1_mcart_1 @ sk_E_1 )
    = ( sk_C @ sk_E_1 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( sk_E_1
    = ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( sk_D_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_E_1
        = ( k4_tarski @ ( sk_C @ sk_E_1 ) @ ( sk_D_1 @ sk_E_1 ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['19','20','21','22'])).

thf('32',plain,(
    ! [X47: $i,X49: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X47 @ X49 ) )
      = X49 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k2_mcart_1 @ sk_E_1 )
        = ( sk_D_1 @ sk_E_1 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k2_mcart_1 @ sk_E_1 )
        = ( sk_D_1 @ sk_E_1 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k2_mcart_1 @ sk_E_1 )
        = ( sk_D_1 @ sk_E_1 ) )
      | ( ( k2_mcart_1 @ sk_E_1 )
        = ( sk_D_1 @ sk_E_1 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_mcart_1 @ sk_E_1 )
        = ( sk_D_1 @ sk_E_1 ) )
      | ( X1 = X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( k2_mcart_1 @ sk_E_1 )
    = ( sk_D_1 @ sk_E_1 ) ),
    inference(condensation,[status(thm)],['36'])).

thf('38',plain,
    ( sk_E_1
    = ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_mcart_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['30','37'])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1 ) )
    | ( r2_hidden @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('40',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k3_zfmisc_1 @ X23 @ X24 @ X25 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('41',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X30 ) @ X31 )
      | ~ ( r2_hidden @ X30 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1 ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X33: $i] :
      ( ( X33 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_2 @ X33 ) @ X33 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X10 @ X9 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('51',plain,
    ( ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1 ) )
    | ( v1_xboole_0 @ sk_E_1 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1 ) )
      | ( v1_xboole_0 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_E_1 )
      | ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( v1_xboole_0 @ sk_E_1 )
    | ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference(condensation,[status(thm)],['53'])).

thf('55',plain,
    ( sk_E_1
    = ( k4_tarski @ ( sk_C @ sk_E_1 ) @ ( sk_D_1 @ sk_E_1 ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf(fc1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( v1_xboole_0 @ ( k4_tarski @ A @ B ) ) )).

thf('56',plain,(
    ! [X3: $i,X4: $i] :
      ~ ( v1_xboole_0 @ ( k4_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc1_zfmisc_1])).

thf('57',plain,(
    ~ ( v1_xboole_0 @ sk_E_1 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['54','57'])).

thf('59',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_3 ) ),
    inference(clc,[status(thm)],['43','58'])).

thf(l139_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i,E: $i] :
            ( ( k4_tarski @ D @ E )
           != A ) ) )).

thf('60',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k4_tarski @ ( sk_D @ X5 ) @ ( sk_E @ X5 ) )
        = X5 )
      | ~ ( r2_hidden @ X5 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('61',plain,
    ( ( k4_tarski @ ( sk_D @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) )
    = ( k1_mcart_1 @ sk_E_1 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k4_tarski @ ( sk_D @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) )
    = ( k1_mcart_1 @ sk_E_1 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('63',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X47 @ X48 ) )
      = X47 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('64',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
    = ( sk_D @ ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) )
    = ( k1_mcart_1 @ sk_E_1 ) ),
    inference(demod,[status(thm)],['61','64'])).

thf('66',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) )
    = ( k1_mcart_1 @ sk_E_1 ) ),
    inference(demod,[status(thm)],['61','64'])).

thf('67',plain,(
    ! [X47: $i,X49: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X47 @ X49 ) )
      = X49 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('68',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
    = ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
    = ( k1_mcart_1 @ sk_E_1 ) ),
    inference(demod,[status(thm)],['65','68'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('70',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k3_mcart_1 @ X20 @ X21 @ X22 )
      = ( k4_tarski @ ( k4_tarski @ X20 @ X21 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ X0 )
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_3 ) ),
    inference(clc,[status(thm)],['43','58'])).

thf('73',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X30 ) @ X32 )
      | ~ ( r2_hidden @ X30 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('74',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_3 ),
    inference('sup-',[status(thm)],['72','73'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('75',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ X11 @ X12 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('76',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_3 ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X50 @ sk_B_3 )
      | ( sk_E_1
       != ( k3_mcart_1 @ X51 @ X50 @ X52 ) )
      | ( sk_D_2 = X52 )
      | ~ ( m1_subset_1 @ X52 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X51 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C_1 )
      | ( sk_D_2 = X1 )
      | ( sk_E_1
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( sk_E_1
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ X0 ) )
      | ( sk_D_2 = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','78'])).

thf('80',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_3 ) ),
    inference(clc,[status(thm)],['43','58'])).

thf('81',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X30 ) @ X31 )
      | ~ ( r2_hidden @ X30 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('82',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ X11 @ X12 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('84',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( sk_E_1
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ X0 ) )
      | ( sk_D_2 = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['79','84'])).

thf('86',plain,
    ( ( sk_E_1 != sk_E_1 )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C_1 )
    | ( sk_D_2
      = ( k2_mcart_1 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['38','85'])).

thf('87',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1 ) )
    | ( r2_hidden @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('88',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k3_zfmisc_1 @ X23 @ X24 @ X25 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('89',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X30 ) @ X32 )
      | ~ ( r2_hidden @ X30 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1 ) )
    | ( r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['87','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C_1 )
      | ( ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k4_zfmisc_1 @ X26 @ X27 @ X28 @ X29 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X26 @ X27 @ X28 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C_1 )
      | ( ( k4_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( ( k4_zfmisc_1 @ X42 @ X43 @ X44 @ X45 )
       != k1_xboole_0 )
      | ( X45 = k1_xboole_0 )
      | ( X44 = k1_xboole_0 )
      | ( X43 = k1_xboole_0 )
      | ( X42 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C_1 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_3 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( sk_B_3 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    sk_B_3 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['98','99','100','101'])).

thf('103',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ X11 @ X12 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('105',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X3: $i,X4: $i] :
      ~ ( v1_xboole_0 @ ( k4_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc1_zfmisc_1])).

thf('108',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( sk_E_1 != sk_E_1 )
    | ( sk_D_2
      = ( k2_mcart_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['86','108'])).

thf('110',plain,
    ( sk_D_2
    = ( k2_mcart_1 @ sk_E_1 ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    sk_D_2
 != ( k7_mcart_1 @ sk_A @ sk_B_3 @ sk_C_1 @ sk_E_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1 ) ),
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

thf('113',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( X38 = k1_xboole_0 )
      | ( X39 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X38 @ X39 @ X41 @ X40 )
        = ( k2_mcart_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k3_zfmisc_1 @ X38 @ X39 @ X41 ) )
      | ( X41 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('114',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_3 @ sk_C_1 @ sk_E_1 )
      = ( k2_mcart_1 @ sk_E_1 ) )
    | ( sk_B_3 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    sk_B_3 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_3 @ sk_C_1 @ sk_E_1 )
    = ( k2_mcart_1 @ sk_E_1 ) ),
    inference('simplify_reflect-',[status(thm)],['114','115','116','117'])).

thf('119',plain,(
    sk_D_2
 != ( k2_mcart_1 @ sk_E_1 ) ),
    inference(demod,[status(thm)],['111','118'])).

thf('120',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['110','119'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.j4oCrlRitV
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:03:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.82/1.03  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.82/1.03  % Solved by: fo/fo7.sh
% 0.82/1.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.82/1.03  % done 950 iterations in 0.575s
% 0.82/1.03  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.82/1.03  % SZS output start Refutation
% 0.82/1.03  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.82/1.03  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.82/1.03  thf(sk_B_2_type, type, sk_B_2: $i > $i).
% 0.82/1.03  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.82/1.03  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.82/1.03  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.82/1.03  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.82/1.03  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.82/1.03  thf(sk_D_type, type, sk_D: $i > $i).
% 0.82/1.03  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.82/1.03  thf(sk_C_type, type, sk_C: $i > $i).
% 0.82/1.03  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.82/1.03  thf(sk_D_1_type, type, sk_D_1: $i > $i).
% 0.82/1.03  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.82/1.03  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.82/1.03  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.82/1.03  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.82/1.03  thf(sk_B_3_type, type, sk_B_3: $i).
% 0.82/1.03  thf(sk_E_type, type, sk_E: $i > $i).
% 0.82/1.03  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.82/1.03  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.82/1.03  thf(sk_A_type, type, sk_A: $i).
% 0.82/1.03  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.82/1.03  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.82/1.03  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.82/1.03  thf(sk_E_1_type, type, sk_E_1: $i).
% 0.82/1.03  thf(t71_mcart_1, conjecture,
% 0.82/1.03    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.82/1.03     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.82/1.03       ( ( ![F:$i]:
% 0.82/1.03           ( ( m1_subset_1 @ F @ A ) =>
% 0.82/1.03             ( ![G:$i]:
% 0.82/1.03               ( ( m1_subset_1 @ G @ B ) =>
% 0.82/1.03                 ( ![H:$i]:
% 0.82/1.03                   ( ( m1_subset_1 @ H @ C ) =>
% 0.82/1.03                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.82/1.03                       ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 0.82/1.03         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.82/1.03           ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.82/1.03           ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 0.82/1.03  thf(zf_stmt_0, negated_conjecture,
% 0.82/1.03    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.82/1.03        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.82/1.03          ( ( ![F:$i]:
% 0.82/1.03              ( ( m1_subset_1 @ F @ A ) =>
% 0.82/1.03                ( ![G:$i]:
% 0.82/1.03                  ( ( m1_subset_1 @ G @ B ) =>
% 0.82/1.03                    ( ![H:$i]:
% 0.82/1.03                      ( ( m1_subset_1 @ H @ C ) =>
% 0.82/1.03                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.82/1.03                          ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 0.82/1.03            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.82/1.03              ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.82/1.03              ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 0.82/1.03    inference('cnf.neg', [status(esa)], [t71_mcart_1])).
% 0.82/1.03  thf('0', plain,
% 0.82/1.03      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf(d2_subset_1, axiom,
% 0.82/1.03    (![A:$i,B:$i]:
% 0.82/1.03     ( ( ( v1_xboole_0 @ A ) =>
% 0.82/1.03         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.82/1.03       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.82/1.03         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.82/1.03  thf('1', plain,
% 0.82/1.03      (![X8 : $i, X9 : $i]:
% 0.82/1.03         (~ (m1_subset_1 @ X8 @ X9)
% 0.82/1.03          | (r2_hidden @ X8 @ X9)
% 0.82/1.03          | (v1_xboole_0 @ X9))),
% 0.82/1.03      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.82/1.03  thf('2', plain,
% 0.82/1.03      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1))
% 0.82/1.03        | (r2_hidden @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 0.82/1.03      inference('sup-', [status(thm)], ['0', '1'])).
% 0.82/1.03  thf(d1_relat_1, axiom,
% 0.82/1.03    (![A:$i]:
% 0.82/1.03     ( ( v1_relat_1 @ A ) <=>
% 0.82/1.03       ( ![B:$i]:
% 0.82/1.03         ( ~( ( r2_hidden @ B @ A ) & 
% 0.82/1.03              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.82/1.03  thf('3', plain,
% 0.82/1.03      (![X13 : $i, X14 : $i]:
% 0.82/1.03         (((X13) = (k4_tarski @ (sk_C @ X13) @ (sk_D_1 @ X13)))
% 0.82/1.03          | ~ (r2_hidden @ X13 @ X14)
% 0.82/1.03          | ~ (v1_relat_1 @ X14))),
% 0.82/1.03      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.82/1.03  thf('4', plain,
% 0.82/1.03      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1))
% 0.82/1.03        | ~ (v1_relat_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1))
% 0.82/1.03        | ((sk_E_1) = (k4_tarski @ (sk_C @ sk_E_1) @ (sk_D_1 @ sk_E_1))))),
% 0.82/1.03      inference('sup-', [status(thm)], ['2', '3'])).
% 0.82/1.03  thf(d3_zfmisc_1, axiom,
% 0.82/1.03    (![A:$i,B:$i,C:$i]:
% 0.82/1.03     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.82/1.03       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.82/1.03  thf('5', plain,
% 0.82/1.03      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.82/1.03         ((k3_zfmisc_1 @ X23 @ X24 @ X25)
% 0.82/1.03           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24) @ X25))),
% 0.82/1.03      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.82/1.03  thf(fc6_relat_1, axiom,
% 0.82/1.03    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.82/1.03  thf('6', plain,
% 0.82/1.03      (![X18 : $i, X19 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19))),
% 0.82/1.03      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.82/1.03  thf('7', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.03         (v1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))),
% 0.82/1.03      inference('sup+', [status(thm)], ['5', '6'])).
% 0.82/1.03  thf('8', plain,
% 0.82/1.03      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1))
% 0.82/1.03        | ((sk_E_1) = (k4_tarski @ (sk_C @ sk_E_1) @ (sk_D_1 @ sk_E_1))))),
% 0.82/1.03      inference('demod', [status(thm)], ['4', '7'])).
% 0.82/1.03  thf(t34_mcart_1, axiom,
% 0.82/1.03    (![A:$i]:
% 0.82/1.03     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.82/1.03          ( ![B:$i]:
% 0.82/1.03            ( ~( ( r2_hidden @ B @ A ) & 
% 0.82/1.03                 ( ![C:$i,D:$i,E:$i,F:$i]:
% 0.82/1.03                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.82/1.03                        ( ( B ) = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) ) ) ) ) ))).
% 0.82/1.03  thf('9', plain,
% 0.82/1.03      (![X33 : $i]:
% 0.82/1.03         (((X33) = (k1_xboole_0)) | (r2_hidden @ (sk_B_2 @ X33) @ X33))),
% 0.82/1.03      inference('cnf', [status(esa)], [t34_mcart_1])).
% 0.82/1.03  thf(t10_mcart_1, axiom,
% 0.82/1.03    (![A:$i,B:$i,C:$i]:
% 0.82/1.03     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.82/1.03       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.82/1.03         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.82/1.03  thf('10', plain,
% 0.82/1.03      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.82/1.03         ((r2_hidden @ (k1_mcart_1 @ X30) @ X31)
% 0.82/1.03          | ~ (r2_hidden @ X30 @ (k2_zfmisc_1 @ X31 @ X32)))),
% 0.82/1.03      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.82/1.03  thf('11', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i]:
% 0.82/1.03         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 0.82/1.03          | (r2_hidden @ (k1_mcart_1 @ (sk_B_2 @ (k2_zfmisc_1 @ X1 @ X0))) @ X1))),
% 0.82/1.03      inference('sup-', [status(thm)], ['9', '10'])).
% 0.82/1.03  thf(d1_xboole_0, axiom,
% 0.82/1.03    (![A:$i]:
% 0.82/1.03     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.82/1.03  thf('12', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.82/1.03      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.82/1.03  thf('13', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i]:
% 0.82/1.03         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.82/1.03      inference('sup-', [status(thm)], ['11', '12'])).
% 0.82/1.03  thf('14', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         (((sk_E_1) = (k4_tarski @ (sk_C @ sk_E_1) @ (sk_D_1 @ sk_E_1)))
% 0.82/1.03          | ((k2_zfmisc_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1) @ X0)
% 0.82/1.03              = (k1_xboole_0)))),
% 0.82/1.03      inference('sup-', [status(thm)], ['8', '13'])).
% 0.82/1.03  thf(d4_zfmisc_1, axiom,
% 0.82/1.03    (![A:$i,B:$i,C:$i,D:$i]:
% 0.82/1.03     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.82/1.03       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.82/1.03  thf('15', plain,
% 0.82/1.03      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.82/1.03         ((k4_zfmisc_1 @ X26 @ X27 @ X28 @ X29)
% 0.82/1.03           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X26 @ X27 @ X28) @ X29))),
% 0.82/1.03      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.82/1.03  thf('16', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         (((sk_E_1) = (k4_tarski @ (sk_C @ sk_E_1) @ (sk_D_1 @ sk_E_1)))
% 0.82/1.03          | ((k4_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1 @ X0) = (k1_xboole_0)))),
% 0.82/1.03      inference('demod', [status(thm)], ['14', '15'])).
% 0.82/1.03  thf(t55_mcart_1, axiom,
% 0.82/1.03    (![A:$i,B:$i,C:$i,D:$i]:
% 0.82/1.03     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.82/1.03         ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) ) <=>
% 0.82/1.03       ( ( k4_zfmisc_1 @ A @ B @ C @ D ) != ( k1_xboole_0 ) ) ))).
% 0.82/1.03  thf('17', plain,
% 0.82/1.03      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.82/1.03         (((k4_zfmisc_1 @ X42 @ X43 @ X44 @ X45) != (k1_xboole_0))
% 0.82/1.03          | ((X45) = (k1_xboole_0))
% 0.82/1.03          | ((X44) = (k1_xboole_0))
% 0.82/1.03          | ((X43) = (k1_xboole_0))
% 0.82/1.03          | ((X42) = (k1_xboole_0)))),
% 0.82/1.03      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.82/1.03  thf('18', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         (((k1_xboole_0) != (k1_xboole_0))
% 0.82/1.03          | ((sk_E_1) = (k4_tarski @ (sk_C @ sk_E_1) @ (sk_D_1 @ sk_E_1)))
% 0.82/1.03          | ((sk_A) = (k1_xboole_0))
% 0.82/1.03          | ((sk_B_3) = (k1_xboole_0))
% 0.82/1.03          | ((sk_C_1) = (k1_xboole_0))
% 0.82/1.03          | ((X0) = (k1_xboole_0)))),
% 0.82/1.03      inference('sup-', [status(thm)], ['16', '17'])).
% 0.82/1.03  thf('19', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         (((X0) = (k1_xboole_0))
% 0.82/1.03          | ((sk_C_1) = (k1_xboole_0))
% 0.82/1.03          | ((sk_B_3) = (k1_xboole_0))
% 0.82/1.03          | ((sk_A) = (k1_xboole_0))
% 0.82/1.03          | ((sk_E_1) = (k4_tarski @ (sk_C @ sk_E_1) @ (sk_D_1 @ sk_E_1))))),
% 0.82/1.03      inference('simplify', [status(thm)], ['18'])).
% 0.82/1.03  thf('20', plain, (((sk_A) != (k1_xboole_0))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('21', plain, (((sk_B_3) != (k1_xboole_0))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('22', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('23', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         (((X0) = (k1_xboole_0))
% 0.82/1.03          | ((sk_E_1) = (k4_tarski @ (sk_C @ sk_E_1) @ (sk_D_1 @ sk_E_1))))),
% 0.82/1.03      inference('simplify_reflect-', [status(thm)], ['19', '20', '21', '22'])).
% 0.82/1.03  thf('24', plain,
% 0.82/1.03      ((((k1_xboole_0) != (sk_E_1))
% 0.82/1.03        | ((sk_E_1) = (k4_tarski @ (sk_C @ sk_E_1) @ (sk_D_1 @ sk_E_1))))),
% 0.82/1.03      inference('eq_fact', [status(thm)], ['23'])).
% 0.82/1.03  thf('25', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         (((X0) = (k1_xboole_0))
% 0.82/1.03          | ((sk_E_1) = (k4_tarski @ (sk_C @ sk_E_1) @ (sk_D_1 @ sk_E_1))))),
% 0.82/1.03      inference('simplify_reflect-', [status(thm)], ['19', '20', '21', '22'])).
% 0.82/1.03  thf('26', plain,
% 0.82/1.03      (((sk_E_1) = (k4_tarski @ (sk_C @ sk_E_1) @ (sk_D_1 @ sk_E_1)))),
% 0.82/1.03      inference('clc', [status(thm)], ['24', '25'])).
% 0.82/1.03  thf('27', plain,
% 0.82/1.03      (((sk_E_1) = (k4_tarski @ (sk_C @ sk_E_1) @ (sk_D_1 @ sk_E_1)))),
% 0.82/1.03      inference('clc', [status(thm)], ['24', '25'])).
% 0.82/1.03  thf(t7_mcart_1, axiom,
% 0.82/1.03    (![A:$i,B:$i]:
% 0.82/1.03     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.82/1.03       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.82/1.03  thf('28', plain,
% 0.82/1.03      (![X47 : $i, X48 : $i]: ((k1_mcart_1 @ (k4_tarski @ X47 @ X48)) = (X47))),
% 0.82/1.03      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.82/1.03  thf('29', plain, (((k1_mcart_1 @ sk_E_1) = (sk_C @ sk_E_1))),
% 0.82/1.03      inference('sup+', [status(thm)], ['27', '28'])).
% 0.82/1.03  thf('30', plain,
% 0.82/1.03      (((sk_E_1) = (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (sk_D_1 @ sk_E_1)))),
% 0.82/1.03      inference('demod', [status(thm)], ['26', '29'])).
% 0.82/1.03  thf('31', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         (((X0) = (k1_xboole_0))
% 0.82/1.03          | ((sk_E_1) = (k4_tarski @ (sk_C @ sk_E_1) @ (sk_D_1 @ sk_E_1))))),
% 0.82/1.03      inference('simplify_reflect-', [status(thm)], ['19', '20', '21', '22'])).
% 0.82/1.03  thf('32', plain,
% 0.82/1.03      (![X47 : $i, X49 : $i]: ((k2_mcart_1 @ (k4_tarski @ X47 @ X49)) = (X49))),
% 0.82/1.03      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.82/1.03  thf('33', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         (((k2_mcart_1 @ sk_E_1) = (sk_D_1 @ sk_E_1)) | ((X0) = (k1_xboole_0)))),
% 0.82/1.03      inference('sup+', [status(thm)], ['31', '32'])).
% 0.82/1.03  thf('34', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         (((k2_mcart_1 @ sk_E_1) = (sk_D_1 @ sk_E_1)) | ((X0) = (k1_xboole_0)))),
% 0.82/1.03      inference('sup+', [status(thm)], ['31', '32'])).
% 0.82/1.03  thf('35', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i]:
% 0.82/1.03         (((X1) = (X0))
% 0.82/1.03          | ((k2_mcart_1 @ sk_E_1) = (sk_D_1 @ sk_E_1))
% 0.82/1.03          | ((k2_mcart_1 @ sk_E_1) = (sk_D_1 @ sk_E_1)))),
% 0.82/1.03      inference('sup+', [status(thm)], ['33', '34'])).
% 0.82/1.03  thf('36', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i]:
% 0.82/1.03         (((k2_mcart_1 @ sk_E_1) = (sk_D_1 @ sk_E_1)) | ((X1) = (X0)))),
% 0.82/1.03      inference('simplify', [status(thm)], ['35'])).
% 0.82/1.03  thf('37', plain, (((k2_mcart_1 @ sk_E_1) = (sk_D_1 @ sk_E_1))),
% 0.82/1.03      inference('condensation', [status(thm)], ['36'])).
% 0.82/1.03  thf('38', plain,
% 0.82/1.03      (((sk_E_1) = (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (k2_mcart_1 @ sk_E_1)))),
% 0.82/1.03      inference('demod', [status(thm)], ['30', '37'])).
% 0.82/1.03  thf('39', plain,
% 0.82/1.03      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1))
% 0.82/1.03        | (r2_hidden @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 0.82/1.03      inference('sup-', [status(thm)], ['0', '1'])).
% 0.82/1.03  thf('40', plain,
% 0.82/1.03      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.82/1.03         ((k3_zfmisc_1 @ X23 @ X24 @ X25)
% 0.82/1.03           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24) @ X25))),
% 0.82/1.03      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.82/1.03  thf('41', plain,
% 0.82/1.03      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.82/1.03         ((r2_hidden @ (k1_mcart_1 @ X30) @ X31)
% 0.82/1.03          | ~ (r2_hidden @ X30 @ (k2_zfmisc_1 @ X31 @ X32)))),
% 0.82/1.03      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.82/1.03  thf('42', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.82/1.03         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.82/1.03          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.82/1.03      inference('sup-', [status(thm)], ['40', '41'])).
% 0.82/1.03  thf('43', plain,
% 0.82/1.03      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1))
% 0.82/1.03        | (r2_hidden @ (k1_mcart_1 @ sk_E_1) @ (k2_zfmisc_1 @ sk_A @ sk_B_3)))),
% 0.82/1.03      inference('sup-', [status(thm)], ['39', '42'])).
% 0.82/1.03  thf('44', plain,
% 0.82/1.03      (![X33 : $i]:
% 0.82/1.03         (((X33) = (k1_xboole_0)) | (r2_hidden @ (sk_B_2 @ X33) @ X33))),
% 0.82/1.03      inference('cnf', [status(esa)], [t34_mcart_1])).
% 0.82/1.03  thf('45', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.82/1.03      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.82/1.03  thf('46', plain,
% 0.82/1.03      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.82/1.03      inference('sup-', [status(thm)], ['44', '45'])).
% 0.82/1.03  thf('47', plain,
% 0.82/1.03      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.82/1.03      inference('sup-', [status(thm)], ['44', '45'])).
% 0.82/1.03  thf('48', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i]:
% 0.82/1.03         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.82/1.03      inference('sup+', [status(thm)], ['46', '47'])).
% 0.82/1.03  thf('49', plain,
% 0.82/1.03      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('50', plain,
% 0.82/1.03      (![X9 : $i, X10 : $i]:
% 0.82/1.03         (~ (m1_subset_1 @ X10 @ X9)
% 0.82/1.03          | (v1_xboole_0 @ X10)
% 0.82/1.03          | ~ (v1_xboole_0 @ X9))),
% 0.82/1.03      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.82/1.03  thf('51', plain,
% 0.82/1.03      ((~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1))
% 0.82/1.03        | (v1_xboole_0 @ sk_E_1))),
% 0.82/1.03      inference('sup-', [status(thm)], ['49', '50'])).
% 0.82/1.03  thf('52', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         (~ (v1_xboole_0 @ X0)
% 0.82/1.03          | ~ (v1_xboole_0 @ X0)
% 0.82/1.03          | ~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1))
% 0.82/1.03          | (v1_xboole_0 @ sk_E_1))),
% 0.82/1.03      inference('sup-', [status(thm)], ['48', '51'])).
% 0.82/1.03  thf('53', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         ((v1_xboole_0 @ sk_E_1)
% 0.82/1.03          | ~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1))
% 0.82/1.03          | ~ (v1_xboole_0 @ X0))),
% 0.82/1.03      inference('simplify', [status(thm)], ['52'])).
% 0.82/1.03  thf('54', plain,
% 0.82/1.03      (((v1_xboole_0 @ sk_E_1)
% 0.82/1.03        | ~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 0.82/1.03      inference('condensation', [status(thm)], ['53'])).
% 0.82/1.03  thf('55', plain,
% 0.82/1.03      (((sk_E_1) = (k4_tarski @ (sk_C @ sk_E_1) @ (sk_D_1 @ sk_E_1)))),
% 0.82/1.03      inference('clc', [status(thm)], ['24', '25'])).
% 0.82/1.03  thf(fc1_zfmisc_1, axiom,
% 0.82/1.03    (![A:$i,B:$i]: ( ~( v1_xboole_0 @ ( k4_tarski @ A @ B ) ) ))).
% 0.82/1.03  thf('56', plain,
% 0.82/1.03      (![X3 : $i, X4 : $i]: ~ (v1_xboole_0 @ (k4_tarski @ X3 @ X4))),
% 0.82/1.03      inference('cnf', [status(esa)], [fc1_zfmisc_1])).
% 0.82/1.03  thf('57', plain, (~ (v1_xboole_0 @ sk_E_1)),
% 0.82/1.03      inference('sup-', [status(thm)], ['55', '56'])).
% 0.82/1.03  thf('58', plain, (~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1))),
% 0.82/1.03      inference('clc', [status(thm)], ['54', '57'])).
% 0.82/1.03  thf('59', plain,
% 0.82/1.03      ((r2_hidden @ (k1_mcart_1 @ sk_E_1) @ (k2_zfmisc_1 @ sk_A @ sk_B_3))),
% 0.82/1.03      inference('clc', [status(thm)], ['43', '58'])).
% 0.82/1.03  thf(l139_zfmisc_1, axiom,
% 0.82/1.03    (![A:$i,B:$i,C:$i]:
% 0.82/1.03     ( ~( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.82/1.03          ( ![D:$i,E:$i]: ( ( k4_tarski @ D @ E ) != ( A ) ) ) ) ))).
% 0.82/1.03  thf('60', plain,
% 0.82/1.03      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.82/1.03         (((k4_tarski @ (sk_D @ X5) @ (sk_E @ X5)) = (X5))
% 0.82/1.03          | ~ (r2_hidden @ X5 @ (k2_zfmisc_1 @ X6 @ X7)))),
% 0.82/1.03      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 0.82/1.03  thf('61', plain,
% 0.82/1.03      (((k4_tarski @ (sk_D @ (k1_mcart_1 @ sk_E_1)) @ 
% 0.82/1.03         (sk_E @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1))),
% 0.82/1.03      inference('sup-', [status(thm)], ['59', '60'])).
% 0.82/1.03  thf('62', plain,
% 0.82/1.03      (((k4_tarski @ (sk_D @ (k1_mcart_1 @ sk_E_1)) @ 
% 0.82/1.03         (sk_E @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1))),
% 0.82/1.03      inference('sup-', [status(thm)], ['59', '60'])).
% 0.82/1.03  thf('63', plain,
% 0.82/1.03      (![X47 : $i, X48 : $i]: ((k1_mcart_1 @ (k4_tarski @ X47 @ X48)) = (X47))),
% 0.82/1.03      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.82/1.03  thf('64', plain,
% 0.82/1.03      (((k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) = (sk_D @ (k1_mcart_1 @ sk_E_1)))),
% 0.82/1.03      inference('sup+', [status(thm)], ['62', '63'])).
% 0.82/1.03  thf('65', plain,
% 0.82/1.03      (((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 0.82/1.03         (sk_E @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1))),
% 0.82/1.03      inference('demod', [status(thm)], ['61', '64'])).
% 0.82/1.03  thf('66', plain,
% 0.82/1.03      (((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 0.82/1.03         (sk_E @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1))),
% 0.82/1.03      inference('demod', [status(thm)], ['61', '64'])).
% 0.82/1.03  thf('67', plain,
% 0.82/1.03      (![X47 : $i, X49 : $i]: ((k2_mcart_1 @ (k4_tarski @ X47 @ X49)) = (X49))),
% 0.82/1.03      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.82/1.03  thf('68', plain,
% 0.82/1.03      (((k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) = (sk_E @ (k1_mcart_1 @ sk_E_1)))),
% 0.82/1.03      inference('sup+', [status(thm)], ['66', '67'])).
% 0.82/1.03  thf('69', plain,
% 0.82/1.03      (((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 0.82/1.03         (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1))),
% 0.82/1.03      inference('demod', [status(thm)], ['65', '68'])).
% 0.82/1.03  thf(d3_mcart_1, axiom,
% 0.82/1.03    (![A:$i,B:$i,C:$i]:
% 0.82/1.03     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.82/1.03  thf('70', plain,
% 0.82/1.03      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.82/1.03         ((k3_mcart_1 @ X20 @ X21 @ X22)
% 0.82/1.03           = (k4_tarski @ (k4_tarski @ X20 @ X21) @ X22))),
% 0.82/1.03      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.82/1.03  thf('71', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         ((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 0.82/1.03           (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ X0)
% 0.82/1.03           = (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ X0))),
% 0.82/1.03      inference('sup+', [status(thm)], ['69', '70'])).
% 0.82/1.03  thf('72', plain,
% 0.82/1.03      ((r2_hidden @ (k1_mcart_1 @ sk_E_1) @ (k2_zfmisc_1 @ sk_A @ sk_B_3))),
% 0.82/1.03      inference('clc', [status(thm)], ['43', '58'])).
% 0.82/1.03  thf('73', plain,
% 0.82/1.03      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.82/1.03         ((r2_hidden @ (k2_mcart_1 @ X30) @ X32)
% 0.82/1.03          | ~ (r2_hidden @ X30 @ (k2_zfmisc_1 @ X31 @ X32)))),
% 0.82/1.03      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.82/1.03  thf('74', plain,
% 0.82/1.03      ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_3)),
% 0.82/1.03      inference('sup-', [status(thm)], ['72', '73'])).
% 0.82/1.03  thf(t1_subset, axiom,
% 0.82/1.03    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.82/1.03  thf('75', plain,
% 0.82/1.03      (![X11 : $i, X12 : $i]:
% 0.82/1.03         ((m1_subset_1 @ X11 @ X12) | ~ (r2_hidden @ X11 @ X12))),
% 0.82/1.03      inference('cnf', [status(esa)], [t1_subset])).
% 0.82/1.03  thf('76', plain,
% 0.82/1.03      ((m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_3)),
% 0.82/1.03      inference('sup-', [status(thm)], ['74', '75'])).
% 0.82/1.03  thf('77', plain,
% 0.82/1.03      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.82/1.03         (~ (m1_subset_1 @ X50 @ sk_B_3)
% 0.82/1.03          | ((sk_E_1) != (k3_mcart_1 @ X51 @ X50 @ X52))
% 0.82/1.03          | ((sk_D_2) = (X52))
% 0.82/1.03          | ~ (m1_subset_1 @ X52 @ sk_C_1)
% 0.82/1.03          | ~ (m1_subset_1 @ X51 @ sk_A))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('78', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i]:
% 0.82/1.03         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.82/1.03          | ~ (m1_subset_1 @ X1 @ sk_C_1)
% 0.82/1.03          | ((sk_D_2) = (X1))
% 0.82/1.03          | ((sk_E_1)
% 0.82/1.03              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ X1)))),
% 0.82/1.03      inference('sup-', [status(thm)], ['76', '77'])).
% 0.82/1.03  thf('79', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         (((sk_E_1) != (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ X0))
% 0.82/1.03          | ((sk_D_2) = (X0))
% 0.82/1.03          | ~ (m1_subset_1 @ X0 @ sk_C_1)
% 0.82/1.03          | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A))),
% 0.82/1.03      inference('sup-', [status(thm)], ['71', '78'])).
% 0.82/1.03  thf('80', plain,
% 0.82/1.03      ((r2_hidden @ (k1_mcart_1 @ sk_E_1) @ (k2_zfmisc_1 @ sk_A @ sk_B_3))),
% 0.82/1.03      inference('clc', [status(thm)], ['43', '58'])).
% 0.82/1.03  thf('81', plain,
% 0.82/1.03      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.82/1.03         ((r2_hidden @ (k1_mcart_1 @ X30) @ X31)
% 0.82/1.03          | ~ (r2_hidden @ X30 @ (k2_zfmisc_1 @ X31 @ X32)))),
% 0.82/1.03      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.82/1.03  thf('82', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A)),
% 0.82/1.03      inference('sup-', [status(thm)], ['80', '81'])).
% 0.82/1.03  thf('83', plain,
% 0.82/1.03      (![X11 : $i, X12 : $i]:
% 0.82/1.03         ((m1_subset_1 @ X11 @ X12) | ~ (r2_hidden @ X11 @ X12))),
% 0.82/1.03      inference('cnf', [status(esa)], [t1_subset])).
% 0.82/1.03  thf('84', plain,
% 0.82/1.03      ((m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A)),
% 0.82/1.03      inference('sup-', [status(thm)], ['82', '83'])).
% 0.82/1.03  thf('85', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         (((sk_E_1) != (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ X0))
% 0.82/1.03          | ((sk_D_2) = (X0))
% 0.82/1.03          | ~ (m1_subset_1 @ X0 @ sk_C_1))),
% 0.82/1.03      inference('demod', [status(thm)], ['79', '84'])).
% 0.82/1.03  thf('86', plain,
% 0.82/1.03      ((((sk_E_1) != (sk_E_1))
% 0.82/1.03        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E_1) @ sk_C_1)
% 0.82/1.03        | ((sk_D_2) = (k2_mcart_1 @ sk_E_1)))),
% 0.82/1.03      inference('sup-', [status(thm)], ['38', '85'])).
% 0.82/1.03  thf('87', plain,
% 0.82/1.03      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1))
% 0.82/1.03        | (r2_hidden @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1)))),
% 0.82/1.03      inference('sup-', [status(thm)], ['0', '1'])).
% 0.82/1.03  thf('88', plain,
% 0.82/1.03      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.82/1.03         ((k3_zfmisc_1 @ X23 @ X24 @ X25)
% 0.82/1.03           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24) @ X25))),
% 0.82/1.03      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.82/1.03  thf('89', plain,
% 0.82/1.03      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.82/1.03         ((r2_hidden @ (k2_mcart_1 @ X30) @ X32)
% 0.82/1.03          | ~ (r2_hidden @ X30 @ (k2_zfmisc_1 @ X31 @ X32)))),
% 0.82/1.03      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.82/1.03  thf('90', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.82/1.03         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.82/1.03          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 0.82/1.03      inference('sup-', [status(thm)], ['88', '89'])).
% 0.82/1.03  thf('91', plain,
% 0.82/1.03      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1))
% 0.82/1.03        | (r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C_1))),
% 0.82/1.03      inference('sup-', [status(thm)], ['87', '90'])).
% 0.82/1.03  thf('92', plain,
% 0.82/1.03      (![X0 : $i, X1 : $i]:
% 0.82/1.03         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.82/1.03      inference('sup-', [status(thm)], ['11', '12'])).
% 0.82/1.03  thf('93', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         ((r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C_1)
% 0.82/1.03          | ((k2_zfmisc_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1) @ X0)
% 0.82/1.03              = (k1_xboole_0)))),
% 0.82/1.03      inference('sup-', [status(thm)], ['91', '92'])).
% 0.82/1.03  thf('94', plain,
% 0.82/1.03      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.82/1.03         ((k4_zfmisc_1 @ X26 @ X27 @ X28 @ X29)
% 0.82/1.03           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X26 @ X27 @ X28) @ X29))),
% 0.82/1.03      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.82/1.03  thf('95', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         ((r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C_1)
% 0.82/1.03          | ((k4_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1 @ X0) = (k1_xboole_0)))),
% 0.82/1.03      inference('demod', [status(thm)], ['93', '94'])).
% 0.82/1.03  thf('96', plain,
% 0.82/1.03      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.82/1.03         (((k4_zfmisc_1 @ X42 @ X43 @ X44 @ X45) != (k1_xboole_0))
% 0.82/1.03          | ((X45) = (k1_xboole_0))
% 0.82/1.03          | ((X44) = (k1_xboole_0))
% 0.82/1.03          | ((X43) = (k1_xboole_0))
% 0.82/1.03          | ((X42) = (k1_xboole_0)))),
% 0.82/1.03      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.82/1.03  thf('97', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         (((k1_xboole_0) != (k1_xboole_0))
% 0.82/1.03          | (r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C_1)
% 0.82/1.03          | ((sk_A) = (k1_xboole_0))
% 0.82/1.03          | ((sk_B_3) = (k1_xboole_0))
% 0.82/1.03          | ((sk_C_1) = (k1_xboole_0))
% 0.82/1.03          | ((X0) = (k1_xboole_0)))),
% 0.82/1.03      inference('sup-', [status(thm)], ['95', '96'])).
% 0.82/1.03  thf('98', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         (((X0) = (k1_xboole_0))
% 0.82/1.03          | ((sk_C_1) = (k1_xboole_0))
% 0.82/1.03          | ((sk_B_3) = (k1_xboole_0))
% 0.82/1.03          | ((sk_A) = (k1_xboole_0))
% 0.82/1.03          | (r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C_1))),
% 0.82/1.03      inference('simplify', [status(thm)], ['97'])).
% 0.82/1.03  thf('99', plain, (((sk_A) != (k1_xboole_0))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('100', plain, (((sk_B_3) != (k1_xboole_0))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('101', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('102', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         (((X0) = (k1_xboole_0)) | (r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C_1))),
% 0.82/1.03      inference('simplify_reflect-', [status(thm)], ['98', '99', '100', '101'])).
% 0.82/1.03  thf('103', plain,
% 0.82/1.03      (![X11 : $i, X12 : $i]:
% 0.82/1.03         ((m1_subset_1 @ X11 @ X12) | ~ (r2_hidden @ X11 @ X12))),
% 0.82/1.03      inference('cnf', [status(esa)], [t1_subset])).
% 0.82/1.03  thf('104', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         (((X0) = (k1_xboole_0))
% 0.82/1.03          | (m1_subset_1 @ (k2_mcart_1 @ sk_E_1) @ sk_C_1))),
% 0.82/1.03      inference('sup-', [status(thm)], ['102', '103'])).
% 0.82/1.03  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.82/1.03  thf('105', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.82/1.03      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.82/1.03  thf('106', plain,
% 0.82/1.03      (![X0 : $i]:
% 0.82/1.03         ((v1_xboole_0 @ X0) | (m1_subset_1 @ (k2_mcart_1 @ sk_E_1) @ sk_C_1))),
% 0.82/1.03      inference('sup+', [status(thm)], ['104', '105'])).
% 0.82/1.03  thf('107', plain,
% 0.82/1.03      (![X3 : $i, X4 : $i]: ~ (v1_xboole_0 @ (k4_tarski @ X3 @ X4))),
% 0.82/1.03      inference('cnf', [status(esa)], [fc1_zfmisc_1])).
% 0.82/1.03  thf('108', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_E_1) @ sk_C_1)),
% 0.82/1.03      inference('sup-', [status(thm)], ['106', '107'])).
% 0.82/1.03  thf('109', plain,
% 0.82/1.03      ((((sk_E_1) != (sk_E_1)) | ((sk_D_2) = (k2_mcart_1 @ sk_E_1)))),
% 0.82/1.03      inference('demod', [status(thm)], ['86', '108'])).
% 0.82/1.03  thf('110', plain, (((sk_D_2) = (k2_mcart_1 @ sk_E_1))),
% 0.82/1.03      inference('simplify', [status(thm)], ['109'])).
% 0.82/1.03  thf('111', plain,
% 0.82/1.03      (((sk_D_2) != (k7_mcart_1 @ sk_A @ sk_B_3 @ sk_C_1 @ sk_E_1))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('112', plain,
% 0.82/1.03      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_3 @ sk_C_1))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf(t50_mcart_1, axiom,
% 0.82/1.03    (![A:$i,B:$i,C:$i]:
% 0.82/1.03     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.82/1.03          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.82/1.03          ( ~( ![D:$i]:
% 0.82/1.03               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.82/1.03                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.82/1.03                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.82/1.03                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.82/1.03                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.82/1.03                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.82/1.03  thf('113', plain,
% 0.82/1.03      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.82/1.03         (((X38) = (k1_xboole_0))
% 0.82/1.03          | ((X39) = (k1_xboole_0))
% 0.82/1.03          | ((k7_mcart_1 @ X38 @ X39 @ X41 @ X40) = (k2_mcart_1 @ X40))
% 0.82/1.03          | ~ (m1_subset_1 @ X40 @ (k3_zfmisc_1 @ X38 @ X39 @ X41))
% 0.82/1.03          | ((X41) = (k1_xboole_0)))),
% 0.82/1.03      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.82/1.03  thf('114', plain,
% 0.82/1.03      ((((sk_C_1) = (k1_xboole_0))
% 0.82/1.03        | ((k7_mcart_1 @ sk_A @ sk_B_3 @ sk_C_1 @ sk_E_1)
% 0.82/1.03            = (k2_mcart_1 @ sk_E_1))
% 0.82/1.03        | ((sk_B_3) = (k1_xboole_0))
% 0.82/1.03        | ((sk_A) = (k1_xboole_0)))),
% 0.82/1.03      inference('sup-', [status(thm)], ['112', '113'])).
% 0.82/1.03  thf('115', plain, (((sk_A) != (k1_xboole_0))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('116', plain, (((sk_B_3) != (k1_xboole_0))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('117', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.82/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.03  thf('118', plain,
% 0.82/1.03      (((k7_mcart_1 @ sk_A @ sk_B_3 @ sk_C_1 @ sk_E_1) = (k2_mcart_1 @ sk_E_1))),
% 0.82/1.03      inference('simplify_reflect-', [status(thm)],
% 0.82/1.03                ['114', '115', '116', '117'])).
% 0.82/1.03  thf('119', plain, (((sk_D_2) != (k2_mcart_1 @ sk_E_1))),
% 0.82/1.03      inference('demod', [status(thm)], ['111', '118'])).
% 0.82/1.03  thf('120', plain, ($false),
% 0.82/1.03      inference('simplify_reflect-', [status(thm)], ['110', '119'])).
% 0.82/1.03  
% 0.82/1.03  % SZS output end Refutation
% 0.82/1.03  
% 0.82/1.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
