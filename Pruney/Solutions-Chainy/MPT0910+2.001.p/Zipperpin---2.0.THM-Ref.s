%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uQFMgCsIjz

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:52 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 419 expanded)
%              Number of leaves         :   37 ( 143 expanded)
%              Depth                    :   17
%              Number of atoms          : 1346 (6039 expanded)
%              Number of equality atoms :  169 ( 829 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t35_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) )
    <=> ( ( k3_zfmisc_1 @ A @ B @ C )
       != k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X27: $i,X28: $i,X30: $i] :
      ( ( X28 != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X27 @ X28 @ X30 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('2',plain,(
    ! [X27: $i,X30: $i] :
      ( ( k3_zfmisc_1 @ X27 @ k1_xboole_0 @ X30 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_zfmisc_1 @ X15 @ X16 @ X17 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('4',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_zfmisc_1 @ X15 @ X16 @ X17 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X27: $i,X28: $i,X30: $i] :
      ( ( X30 != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X27 @ X28 @ X30 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('8',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k3_zfmisc_1 @ X27 @ X28 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t70_mcart_1,conjecture,(
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
                     => ( D = G ) ) ) ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( C = k1_xboole_0 )
          | ( D
            = ( k6_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )).

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
                       => ( D = G ) ) ) ) )
         => ( ( A = k1_xboole_0 )
            | ( B = k1_xboole_0 )
            | ( C = k1_xboole_0 )
            | ( D
              = ( k6_mcart_1 @ A @ B @ C @ E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t70_mcart_1])).

thf('13',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','9'])).

thf('16',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(condensation,[status(thm)],['16'])).

thf('18',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('19',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X5 )
      | ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( r2_hidden @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_zfmisc_1 @ X15 @ X16 @ X17 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('22',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X22 ) @ X24 )
      | ~ ( r2_hidden @ X22 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('26',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C_1 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k3_zfmisc_1 @ X27 @ X28 @ X29 )
       != k1_xboole_0 )
      | ( X29 = k1_xboole_0 )
      | ( X28 = k1_xboole_0 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('28',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C_1 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C_1 ),
    inference('simplify_reflect-',[status(thm)],['29','30','31','32'])).

thf('34',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( m1_subset_1 @ X4 @ X5 )
      | ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('35',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( r2_hidden @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('37',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X7
        = ( k4_tarski @ ( sk_C @ X7 ) @ ( sk_D_1 @ X7 ) ) )
      | ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('38',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( sk_E_1
      = ( k4_tarski @ ( sk_C @ sk_E_1 ) @ ( sk_D_1 @ sk_E_1 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_zfmisc_1 @ X15 @ X16 @ X17 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('40',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ X9 )
      | ( r2_hidden @ ( sk_B @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(l139_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i,E: $i] :
            ( ( k4_tarski @ D @ E )
           != A ) ) )).

thf('41',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_tarski @ ( sk_D @ X1 ) @ ( sk_E @ X1 ) )
        = X1 )
      | ~ ( r2_hidden @ X1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( ( k4_tarski @ ( sk_D @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ ( sk_E @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) )
        = ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ( ( sk_B @ X9 )
       != ( k4_tarski @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( v1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','44'])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( sk_E_1
      = ( k4_tarski @ ( sk_C @ sk_E_1 ) @ ( sk_D_1 @ sk_E_1 ) ) ) ),
    inference(demod,[status(thm)],['38','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('48',plain,
    ( ( sk_E_1
      = ( k4_tarski @ ( sk_C @ sk_E_1 ) @ ( sk_D_1 @ sk_E_1 ) ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k3_zfmisc_1 @ X27 @ X28 @ X29 )
       != k1_xboole_0 )
      | ( X29 = k1_xboole_0 )
      | ( X28 = k1_xboole_0 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('50',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_E_1
      = ( k4_tarski @ ( sk_C @ sk_E_1 ) @ ( sk_D_1 @ sk_E_1 ) ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_E_1
      = ( k4_tarski @ ( sk_C @ sk_E_1 ) @ ( sk_D_1 @ sk_E_1 ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( sk_E_1
    = ( k4_tarski @ ( sk_C @ sk_E_1 ) @ ( sk_D_1 @ sk_E_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['51','52','53','54'])).

thf('56',plain,
    ( sk_E_1
    = ( k4_tarski @ ( sk_C @ sk_E_1 ) @ ( sk_D_1 @ sk_E_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['51','52','53','54'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('57',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X35 @ X36 ) )
      = X35 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('58',plain,
    ( ( k1_mcart_1 @ sk_E_1 )
    = ( sk_C @ sk_E_1 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,
    ( sk_E_1
    = ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( sk_D_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['55','58'])).

thf('60',plain,
    ( sk_E_1
    = ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( sk_D_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['55','58'])).

thf('61',plain,(
    ! [X35: $i,X37: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X35 @ X37 ) )
      = X37 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('62',plain,
    ( ( k2_mcart_1 @ sk_E_1 )
    = ( sk_D_1 @ sk_E_1 ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,
    ( sk_E_1
    = ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_mcart_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('64',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( r2_hidden @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('65',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_zfmisc_1 @ X15 @ X16 @ X17 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('66',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X22 ) @ X23 )
      | ~ ( r2_hidden @ X22 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('70',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf(t23_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( A
          = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ) )).

thf('71',plain,(
    ! [X25: $i,X26: $i] :
      ( ( X25
        = ( k4_tarski @ ( k1_mcart_1 @ X25 ) @ ( k2_mcart_1 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X26 )
      | ~ ( r2_hidden @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('72',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( ( k1_mcart_1 @ sk_E_1 )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('74',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( ( k1_mcart_1 @ sk_E_1 )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k3_zfmisc_1 @ X27 @ X28 @ X29 )
       != k1_xboole_0 )
      | ( X29 = k1_xboole_0 )
      | ( X28 = k1_xboole_0 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('76',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_mcart_1 @ sk_E_1 )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k1_mcart_1 @ sk_E_1 )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( k1_mcart_1 @ sk_E_1 )
    = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['77','78','79','80'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('82',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_mcart_1 @ X12 @ X13 @ X14 )
      = ( k4_tarski @ ( k4_tarski @ X12 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ X0 )
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k6_mcart_1 @ A @ B @ C @ D ) @ B ) ) )).

thf('85',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( m1_subset_1 @ ( k6_mcart_1 @ X18 @ X19 @ X20 @ X21 ) @ X19 )
      | ~ ( m1_subset_1 @ X21 @ ( k3_zfmisc_1 @ X18 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_mcart_1])).

thf('86',plain,(
    m1_subset_1 @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ sk_B_1 )
      | ( sk_D_2 = X38 )
      | ( sk_E_1
       != ( k3_mcart_1 @ X39 @ X38 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X39 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C_1 )
      | ( sk_E_1
       != ( k3_mcart_1 @ X0 @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_1 ) @ X1 ) )
      | ( sk_D_2
        = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_1 ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    sk_D_2
 != ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C_1 )
      | ( sk_E_1
       != ( k3_mcart_1 @ X0 @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_1 ) @ X1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['88','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
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

thf('92',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( X31 = k1_xboole_0 )
      | ( X32 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X31 @ X32 @ X34 @ X33 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k3_zfmisc_1 @ X31 @ X32 @ X34 ) )
      | ( X34 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('93',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_1 )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_1 )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['93','94','95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C_1 )
      | ( sk_E_1
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['90','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( sk_E_1
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','98'])).

thf('100',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('101',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X22 ) @ X23 )
      | ~ ( r2_hidden @ X22 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('102',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k3_zfmisc_1 @ X27 @ X28 @ X29 )
       != k1_xboole_0 )
      | ( X29 = k1_xboole_0 )
      | ( X28 = k1_xboole_0 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('104',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['105','106','107','108'])).

thf('110',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( m1_subset_1 @ X4 @ X5 )
      | ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('111',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('113',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','9'])).

thf('116',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['114','115'])).

thf('117',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(condensation,[status(thm)],['116'])).

thf('118',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ),
    inference(clc,[status(thm)],['111','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( sk_E_1
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['99','118'])).

thf('120',plain,
    ( ( sk_E_1 != sk_E_1 )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['63','119'])).

thf('121',plain,(
    ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    v1_xboole_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['35','121'])).

thf('123',plain,(
    $false ),
    inference(demod,[status(thm)],['17','122'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uQFMgCsIjz
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 15:17:06 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 1.37/1.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.37/1.60  % Solved by: fo/fo7.sh
% 1.37/1.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.37/1.60  % done 1863 iterations in 1.119s
% 1.37/1.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.37/1.60  % SZS output start Refutation
% 1.37/1.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.37/1.60  thf(sk_E_1_type, type, sk_E_1: $i).
% 1.37/1.60  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 1.37/1.60  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 1.37/1.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.37/1.60  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 1.37/1.60  thf(sk_C_type, type, sk_C: $i > $i).
% 1.37/1.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.37/1.60  thf(sk_A_type, type, sk_A: $i).
% 1.37/1.60  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.37/1.60  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 1.37/1.60  thf(sk_D_1_type, type, sk_D_1: $i > $i).
% 1.37/1.60  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 1.37/1.60  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 1.37/1.60  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.37/1.60  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 1.37/1.60  thf(sk_D_type, type, sk_D: $i > $i).
% 1.37/1.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.37/1.60  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.37/1.60  thf(sk_D_2_type, type, sk_D_2: $i).
% 1.37/1.60  thf(sk_B_type, type, sk_B: $i > $i).
% 1.37/1.60  thf(sk_E_type, type, sk_E: $i > $i).
% 1.37/1.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.37/1.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.37/1.60  thf(l13_xboole_0, axiom,
% 1.37/1.60    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.37/1.60  thf('0', plain,
% 1.37/1.60      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.37/1.60      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.37/1.60  thf(t35_mcart_1, axiom,
% 1.37/1.60    (![A:$i,B:$i,C:$i]:
% 1.37/1.60     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.37/1.60         ( ( C ) != ( k1_xboole_0 ) ) ) <=>
% 1.37/1.60       ( ( k3_zfmisc_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) ))).
% 1.37/1.60  thf('1', plain,
% 1.37/1.60      (![X27 : $i, X28 : $i, X30 : $i]:
% 1.37/1.60         (((X28) != (k1_xboole_0))
% 1.37/1.60          | ((k3_zfmisc_1 @ X27 @ X28 @ X30) = (k1_xboole_0)))),
% 1.37/1.60      inference('cnf', [status(esa)], [t35_mcart_1])).
% 1.37/1.60  thf('2', plain,
% 1.37/1.60      (![X27 : $i, X30 : $i]:
% 1.37/1.60         ((k3_zfmisc_1 @ X27 @ k1_xboole_0 @ X30) = (k1_xboole_0))),
% 1.37/1.60      inference('simplify', [status(thm)], ['1'])).
% 1.37/1.60  thf(d3_zfmisc_1, axiom,
% 1.37/1.60    (![A:$i,B:$i,C:$i]:
% 1.37/1.60     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 1.37/1.60       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 1.37/1.60  thf('3', plain,
% 1.37/1.60      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.37/1.60         ((k3_zfmisc_1 @ X15 @ X16 @ X17)
% 1.37/1.60           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16) @ X17))),
% 1.37/1.60      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.37/1.60  thf('4', plain,
% 1.37/1.60      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.37/1.60         ((k3_zfmisc_1 @ X15 @ X16 @ X17)
% 1.37/1.60           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16) @ X17))),
% 1.37/1.60      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.37/1.60  thf('5', plain,
% 1.37/1.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.37/1.60         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 1.37/1.60           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 1.37/1.60      inference('sup+', [status(thm)], ['3', '4'])).
% 1.37/1.60  thf('6', plain,
% 1.37/1.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.60         ((k1_xboole_0)
% 1.37/1.60           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ k1_xboole_0) @ X0))),
% 1.37/1.60      inference('sup+', [status(thm)], ['2', '5'])).
% 1.37/1.60  thf('7', plain,
% 1.37/1.60      (![X27 : $i, X28 : $i, X30 : $i]:
% 1.37/1.60         (((X30) != (k1_xboole_0))
% 1.37/1.60          | ((k3_zfmisc_1 @ X27 @ X28 @ X30) = (k1_xboole_0)))),
% 1.37/1.60      inference('cnf', [status(esa)], [t35_mcart_1])).
% 1.37/1.60  thf('8', plain,
% 1.37/1.60      (![X27 : $i, X28 : $i]:
% 1.37/1.60         ((k3_zfmisc_1 @ X27 @ X28 @ k1_xboole_0) = (k1_xboole_0))),
% 1.37/1.60      inference('simplify', [status(thm)], ['7'])).
% 1.37/1.60  thf('9', plain,
% 1.37/1.60      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 1.37/1.60      inference('demod', [status(thm)], ['6', '8'])).
% 1.37/1.60  thf('10', plain,
% 1.37/1.60      (![X0 : $i, X1 : $i]:
% 1.37/1.60         (((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 1.37/1.60      inference('sup+', [status(thm)], ['0', '9'])).
% 1.37/1.60  thf('11', plain,
% 1.37/1.60      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.37/1.60      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.37/1.60  thf('12', plain,
% 1.37/1.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.60         (((X2) = (k2_zfmisc_1 @ X1 @ X0))
% 1.37/1.60          | ~ (v1_xboole_0 @ X1)
% 1.37/1.60          | ~ (v1_xboole_0 @ X2))),
% 1.37/1.60      inference('sup+', [status(thm)], ['10', '11'])).
% 1.37/1.60  thf(t70_mcart_1, conjecture,
% 1.37/1.60    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.37/1.60     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.37/1.60       ( ( ![F:$i]:
% 1.37/1.60           ( ( m1_subset_1 @ F @ A ) =>
% 1.37/1.60             ( ![G:$i]:
% 1.37/1.60               ( ( m1_subset_1 @ G @ B ) =>
% 1.37/1.60                 ( ![H:$i]:
% 1.37/1.60                   ( ( m1_subset_1 @ H @ C ) =>
% 1.37/1.60                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 1.37/1.60                       ( ( D ) = ( G ) ) ) ) ) ) ) ) ) =>
% 1.37/1.60         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.37/1.60           ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.37/1.60           ( ( D ) = ( k6_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 1.37/1.60  thf(zf_stmt_0, negated_conjecture,
% 1.37/1.60    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.37/1.60        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.37/1.60          ( ( ![F:$i]:
% 1.37/1.60              ( ( m1_subset_1 @ F @ A ) =>
% 1.37/1.60                ( ![G:$i]:
% 1.37/1.60                  ( ( m1_subset_1 @ G @ B ) =>
% 1.37/1.60                    ( ![H:$i]:
% 1.37/1.60                      ( ( m1_subset_1 @ H @ C ) =>
% 1.37/1.60                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 1.37/1.60                          ( ( D ) = ( G ) ) ) ) ) ) ) ) ) =>
% 1.37/1.60            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.37/1.60              ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.37/1.60              ( ( D ) = ( k6_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 1.37/1.60    inference('cnf.neg', [status(esa)], [t70_mcart_1])).
% 1.37/1.60  thf('13', plain, (((sk_C_1) != (k1_xboole_0))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('14', plain,
% 1.37/1.60      (![X0 : $i, X1 : $i]:
% 1.37/1.60         (((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0))
% 1.37/1.60          | ~ (v1_xboole_0 @ sk_C_1)
% 1.37/1.60          | ~ (v1_xboole_0 @ X1))),
% 1.37/1.60      inference('sup-', [status(thm)], ['12', '13'])).
% 1.37/1.60  thf('15', plain,
% 1.37/1.60      (![X0 : $i, X1 : $i]:
% 1.37/1.60         (((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 1.37/1.60      inference('sup+', [status(thm)], ['0', '9'])).
% 1.37/1.60  thf('16', plain,
% 1.37/1.60      (![X1 : $i]: (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ sk_C_1))),
% 1.37/1.60      inference('clc', [status(thm)], ['14', '15'])).
% 1.37/1.60  thf('17', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 1.37/1.60      inference('condensation', [status(thm)], ['16'])).
% 1.37/1.60  thf('18', plain,
% 1.37/1.60      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf(d2_subset_1, axiom,
% 1.37/1.60    (![A:$i,B:$i]:
% 1.37/1.60     ( ( ( v1_xboole_0 @ A ) =>
% 1.37/1.60         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.37/1.60       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.37/1.60         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.37/1.60  thf('19', plain,
% 1.37/1.60      (![X4 : $i, X5 : $i]:
% 1.37/1.60         (~ (m1_subset_1 @ X4 @ X5)
% 1.37/1.60          | (r2_hidden @ X4 @ X5)
% 1.37/1.60          | (v1_xboole_0 @ X5))),
% 1.37/1.60      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.37/1.60  thf('20', plain,
% 1.37/1.60      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 1.37/1.60        | (r2_hidden @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 1.37/1.60      inference('sup-', [status(thm)], ['18', '19'])).
% 1.37/1.60  thf('21', plain,
% 1.37/1.60      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.37/1.60         ((k3_zfmisc_1 @ X15 @ X16 @ X17)
% 1.37/1.60           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16) @ X17))),
% 1.37/1.60      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.37/1.60  thf(t10_mcart_1, axiom,
% 1.37/1.60    (![A:$i,B:$i,C:$i]:
% 1.37/1.60     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 1.37/1.60       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 1.37/1.60         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 1.37/1.60  thf('22', plain,
% 1.37/1.60      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.37/1.60         ((r2_hidden @ (k2_mcart_1 @ X22) @ X24)
% 1.37/1.60          | ~ (r2_hidden @ X22 @ (k2_zfmisc_1 @ X23 @ X24)))),
% 1.37/1.60      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.37/1.60  thf('23', plain,
% 1.37/1.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.37/1.60         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.37/1.60          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 1.37/1.60      inference('sup-', [status(thm)], ['21', '22'])).
% 1.37/1.60  thf('24', plain,
% 1.37/1.60      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 1.37/1.60        | (r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C_1))),
% 1.37/1.60      inference('sup-', [status(thm)], ['20', '23'])).
% 1.37/1.60  thf('25', plain,
% 1.37/1.60      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.37/1.60      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.37/1.60  thf('26', plain,
% 1.37/1.60      (((r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C_1)
% 1.37/1.60        | ((k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_xboole_0)))),
% 1.37/1.60      inference('sup-', [status(thm)], ['24', '25'])).
% 1.37/1.60  thf('27', plain,
% 1.37/1.60      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.37/1.60         (((k3_zfmisc_1 @ X27 @ X28 @ X29) != (k1_xboole_0))
% 1.37/1.60          | ((X29) = (k1_xboole_0))
% 1.37/1.60          | ((X28) = (k1_xboole_0))
% 1.37/1.60          | ((X27) = (k1_xboole_0)))),
% 1.37/1.60      inference('cnf', [status(esa)], [t35_mcart_1])).
% 1.37/1.60  thf('28', plain,
% 1.37/1.60      ((((k1_xboole_0) != (k1_xboole_0))
% 1.37/1.60        | (r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C_1)
% 1.37/1.60        | ((sk_A) = (k1_xboole_0))
% 1.37/1.60        | ((sk_B_1) = (k1_xboole_0))
% 1.37/1.60        | ((sk_C_1) = (k1_xboole_0)))),
% 1.37/1.60      inference('sup-', [status(thm)], ['26', '27'])).
% 1.37/1.60  thf('29', plain,
% 1.37/1.60      ((((sk_C_1) = (k1_xboole_0))
% 1.37/1.60        | ((sk_B_1) = (k1_xboole_0))
% 1.37/1.60        | ((sk_A) = (k1_xboole_0))
% 1.37/1.60        | (r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C_1))),
% 1.37/1.60      inference('simplify', [status(thm)], ['28'])).
% 1.37/1.60  thf('30', plain, (((sk_A) != (k1_xboole_0))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('31', plain, (((sk_B_1) != (k1_xboole_0))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('32', plain, (((sk_C_1) != (k1_xboole_0))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('33', plain, ((r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C_1)),
% 1.37/1.60      inference('simplify_reflect-', [status(thm)], ['29', '30', '31', '32'])).
% 1.37/1.60  thf('34', plain,
% 1.37/1.60      (![X4 : $i, X5 : $i]:
% 1.37/1.60         (~ (r2_hidden @ X4 @ X5)
% 1.37/1.60          | (m1_subset_1 @ X4 @ X5)
% 1.37/1.60          | (v1_xboole_0 @ X5))),
% 1.37/1.60      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.37/1.60  thf('35', plain,
% 1.37/1.60      (((v1_xboole_0 @ sk_C_1) | (m1_subset_1 @ (k2_mcart_1 @ sk_E_1) @ sk_C_1))),
% 1.37/1.60      inference('sup-', [status(thm)], ['33', '34'])).
% 1.37/1.60  thf('36', plain,
% 1.37/1.60      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 1.37/1.60        | (r2_hidden @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 1.37/1.60      inference('sup-', [status(thm)], ['18', '19'])).
% 1.37/1.60  thf(d1_relat_1, axiom,
% 1.37/1.60    (![A:$i]:
% 1.37/1.60     ( ( v1_relat_1 @ A ) <=>
% 1.37/1.60       ( ![B:$i]:
% 1.37/1.60         ( ~( ( r2_hidden @ B @ A ) & 
% 1.37/1.60              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 1.37/1.60  thf('37', plain,
% 1.37/1.60      (![X7 : $i, X8 : $i]:
% 1.37/1.60         (((X7) = (k4_tarski @ (sk_C @ X7) @ (sk_D_1 @ X7)))
% 1.37/1.60          | ~ (r2_hidden @ X7 @ X8)
% 1.37/1.60          | ~ (v1_relat_1 @ X8))),
% 1.37/1.60      inference('cnf', [status(esa)], [d1_relat_1])).
% 1.37/1.60  thf('38', plain,
% 1.37/1.60      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 1.37/1.60        | ~ (v1_relat_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 1.37/1.60        | ((sk_E_1) = (k4_tarski @ (sk_C @ sk_E_1) @ (sk_D_1 @ sk_E_1))))),
% 1.37/1.60      inference('sup-', [status(thm)], ['36', '37'])).
% 1.37/1.60  thf('39', plain,
% 1.37/1.60      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.37/1.60         ((k3_zfmisc_1 @ X15 @ X16 @ X17)
% 1.37/1.60           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16) @ X17))),
% 1.37/1.60      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.37/1.60  thf('40', plain,
% 1.37/1.60      (![X9 : $i]: ((v1_relat_1 @ X9) | (r2_hidden @ (sk_B @ X9) @ X9))),
% 1.37/1.60      inference('cnf', [status(esa)], [d1_relat_1])).
% 1.37/1.60  thf(l139_zfmisc_1, axiom,
% 1.37/1.60    (![A:$i,B:$i,C:$i]:
% 1.37/1.60     ( ~( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 1.37/1.60          ( ![D:$i,E:$i]: ( ( k4_tarski @ D @ E ) != ( A ) ) ) ) ))).
% 1.37/1.60  thf('41', plain,
% 1.37/1.60      (![X1 : $i, X2 : $i, X3 : $i]:
% 1.37/1.60         (((k4_tarski @ (sk_D @ X1) @ (sk_E @ X1)) = (X1))
% 1.37/1.60          | ~ (r2_hidden @ X1 @ (k2_zfmisc_1 @ X2 @ X3)))),
% 1.37/1.60      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 1.37/1.60  thf('42', plain,
% 1.37/1.60      (![X0 : $i, X1 : $i]:
% 1.37/1.60         ((v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))
% 1.37/1.60          | ((k4_tarski @ (sk_D @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0))) @ 
% 1.37/1.60              (sk_E @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0))))
% 1.37/1.60              = (sk_B @ (k2_zfmisc_1 @ X1 @ X0))))),
% 1.37/1.60      inference('sup-', [status(thm)], ['40', '41'])).
% 1.37/1.60  thf('43', plain,
% 1.37/1.60      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.37/1.60         ((v1_relat_1 @ X9) | ((sk_B @ X9) != (k4_tarski @ X10 @ X11)))),
% 1.37/1.60      inference('cnf', [status(esa)], [d1_relat_1])).
% 1.37/1.60  thf('44', plain,
% 1.37/1.60      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))),
% 1.37/1.60      inference('clc', [status(thm)], ['42', '43'])).
% 1.37/1.60  thf('45', plain,
% 1.37/1.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.60         (v1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))),
% 1.37/1.60      inference('sup+', [status(thm)], ['39', '44'])).
% 1.37/1.60  thf('46', plain,
% 1.37/1.60      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 1.37/1.60        | ((sk_E_1) = (k4_tarski @ (sk_C @ sk_E_1) @ (sk_D_1 @ sk_E_1))))),
% 1.37/1.60      inference('demod', [status(thm)], ['38', '45'])).
% 1.37/1.60  thf('47', plain,
% 1.37/1.60      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.37/1.60      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.37/1.60  thf('48', plain,
% 1.37/1.60      ((((sk_E_1) = (k4_tarski @ (sk_C @ sk_E_1) @ (sk_D_1 @ sk_E_1)))
% 1.37/1.60        | ((k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_xboole_0)))),
% 1.37/1.60      inference('sup-', [status(thm)], ['46', '47'])).
% 1.37/1.60  thf('49', plain,
% 1.37/1.60      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.37/1.60         (((k3_zfmisc_1 @ X27 @ X28 @ X29) != (k1_xboole_0))
% 1.37/1.60          | ((X29) = (k1_xboole_0))
% 1.37/1.60          | ((X28) = (k1_xboole_0))
% 1.37/1.60          | ((X27) = (k1_xboole_0)))),
% 1.37/1.60      inference('cnf', [status(esa)], [t35_mcart_1])).
% 1.37/1.60  thf('50', plain,
% 1.37/1.60      ((((k1_xboole_0) != (k1_xboole_0))
% 1.37/1.60        | ((sk_E_1) = (k4_tarski @ (sk_C @ sk_E_1) @ (sk_D_1 @ sk_E_1)))
% 1.37/1.60        | ((sk_A) = (k1_xboole_0))
% 1.37/1.60        | ((sk_B_1) = (k1_xboole_0))
% 1.37/1.60        | ((sk_C_1) = (k1_xboole_0)))),
% 1.37/1.60      inference('sup-', [status(thm)], ['48', '49'])).
% 1.37/1.60  thf('51', plain,
% 1.37/1.60      ((((sk_C_1) = (k1_xboole_0))
% 1.37/1.60        | ((sk_B_1) = (k1_xboole_0))
% 1.37/1.60        | ((sk_A) = (k1_xboole_0))
% 1.37/1.60        | ((sk_E_1) = (k4_tarski @ (sk_C @ sk_E_1) @ (sk_D_1 @ sk_E_1))))),
% 1.37/1.60      inference('simplify', [status(thm)], ['50'])).
% 1.37/1.60  thf('52', plain, (((sk_A) != (k1_xboole_0))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('53', plain, (((sk_B_1) != (k1_xboole_0))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('54', plain, (((sk_C_1) != (k1_xboole_0))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('55', plain,
% 1.37/1.60      (((sk_E_1) = (k4_tarski @ (sk_C @ sk_E_1) @ (sk_D_1 @ sk_E_1)))),
% 1.37/1.60      inference('simplify_reflect-', [status(thm)], ['51', '52', '53', '54'])).
% 1.37/1.60  thf('56', plain,
% 1.37/1.60      (((sk_E_1) = (k4_tarski @ (sk_C @ sk_E_1) @ (sk_D_1 @ sk_E_1)))),
% 1.37/1.60      inference('simplify_reflect-', [status(thm)], ['51', '52', '53', '54'])).
% 1.37/1.60  thf(t7_mcart_1, axiom,
% 1.37/1.60    (![A:$i,B:$i]:
% 1.37/1.60     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 1.37/1.60       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 1.37/1.60  thf('57', plain,
% 1.37/1.60      (![X35 : $i, X36 : $i]: ((k1_mcart_1 @ (k4_tarski @ X35 @ X36)) = (X35))),
% 1.37/1.60      inference('cnf', [status(esa)], [t7_mcart_1])).
% 1.37/1.60  thf('58', plain, (((k1_mcart_1 @ sk_E_1) = (sk_C @ sk_E_1))),
% 1.37/1.60      inference('sup+', [status(thm)], ['56', '57'])).
% 1.37/1.60  thf('59', plain,
% 1.37/1.60      (((sk_E_1) = (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (sk_D_1 @ sk_E_1)))),
% 1.37/1.60      inference('demod', [status(thm)], ['55', '58'])).
% 1.37/1.60  thf('60', plain,
% 1.37/1.60      (((sk_E_1) = (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (sk_D_1 @ sk_E_1)))),
% 1.37/1.60      inference('demod', [status(thm)], ['55', '58'])).
% 1.37/1.60  thf('61', plain,
% 1.37/1.60      (![X35 : $i, X37 : $i]: ((k2_mcart_1 @ (k4_tarski @ X35 @ X37)) = (X37))),
% 1.37/1.60      inference('cnf', [status(esa)], [t7_mcart_1])).
% 1.37/1.60  thf('62', plain, (((k2_mcart_1 @ sk_E_1) = (sk_D_1 @ sk_E_1))),
% 1.37/1.60      inference('sup+', [status(thm)], ['60', '61'])).
% 1.37/1.60  thf('63', plain,
% 1.37/1.60      (((sk_E_1) = (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (k2_mcart_1 @ sk_E_1)))),
% 1.37/1.60      inference('demod', [status(thm)], ['59', '62'])).
% 1.37/1.60  thf('64', plain,
% 1.37/1.60      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 1.37/1.60        | (r2_hidden @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 1.37/1.60      inference('sup-', [status(thm)], ['18', '19'])).
% 1.37/1.60  thf('65', plain,
% 1.37/1.60      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.37/1.60         ((k3_zfmisc_1 @ X15 @ X16 @ X17)
% 1.37/1.60           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16) @ X17))),
% 1.37/1.60      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.37/1.60  thf('66', plain,
% 1.37/1.60      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.37/1.60         ((r2_hidden @ (k1_mcart_1 @ X22) @ X23)
% 1.37/1.60          | ~ (r2_hidden @ X22 @ (k2_zfmisc_1 @ X23 @ X24)))),
% 1.37/1.60      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.37/1.60  thf('67', plain,
% 1.37/1.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.37/1.60         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.37/1.60          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 1.37/1.60      inference('sup-', [status(thm)], ['65', '66'])).
% 1.37/1.60  thf('68', plain,
% 1.37/1.60      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 1.37/1.60        | (r2_hidden @ (k1_mcart_1 @ sk_E_1) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.37/1.60      inference('sup-', [status(thm)], ['64', '67'])).
% 1.37/1.60  thf('69', plain,
% 1.37/1.60      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.37/1.60      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.37/1.60  thf('70', plain,
% 1.37/1.60      (((r2_hidden @ (k1_mcart_1 @ sk_E_1) @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 1.37/1.60        | ((k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_xboole_0)))),
% 1.37/1.60      inference('sup-', [status(thm)], ['68', '69'])).
% 1.37/1.60  thf(t23_mcart_1, axiom,
% 1.37/1.60    (![A:$i,B:$i]:
% 1.37/1.60     ( ( v1_relat_1 @ B ) =>
% 1.37/1.60       ( ( r2_hidden @ A @ B ) =>
% 1.37/1.60         ( ( A ) = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ))).
% 1.37/1.60  thf('71', plain,
% 1.37/1.60      (![X25 : $i, X26 : $i]:
% 1.37/1.60         (((X25) = (k4_tarski @ (k1_mcart_1 @ X25) @ (k2_mcart_1 @ X25)))
% 1.37/1.60          | ~ (v1_relat_1 @ X26)
% 1.37/1.60          | ~ (r2_hidden @ X25 @ X26))),
% 1.37/1.60      inference('cnf', [status(esa)], [t23_mcart_1])).
% 1.37/1.60  thf('72', plain,
% 1.37/1.60      ((((k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_xboole_0))
% 1.37/1.60        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 1.37/1.60        | ((k1_mcart_1 @ sk_E_1)
% 1.37/1.60            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 1.37/1.60               (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)))))),
% 1.37/1.60      inference('sup-', [status(thm)], ['70', '71'])).
% 1.37/1.60  thf('73', plain,
% 1.37/1.60      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))),
% 1.37/1.60      inference('clc', [status(thm)], ['42', '43'])).
% 1.37/1.60  thf('74', plain,
% 1.37/1.60      ((((k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_xboole_0))
% 1.37/1.60        | ((k1_mcart_1 @ sk_E_1)
% 1.37/1.60            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 1.37/1.60               (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)))))),
% 1.37/1.60      inference('demod', [status(thm)], ['72', '73'])).
% 1.37/1.60  thf('75', plain,
% 1.37/1.60      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.37/1.60         (((k3_zfmisc_1 @ X27 @ X28 @ X29) != (k1_xboole_0))
% 1.37/1.60          | ((X29) = (k1_xboole_0))
% 1.37/1.60          | ((X28) = (k1_xboole_0))
% 1.37/1.60          | ((X27) = (k1_xboole_0)))),
% 1.37/1.60      inference('cnf', [status(esa)], [t35_mcart_1])).
% 1.37/1.60  thf('76', plain,
% 1.37/1.60      ((((k1_xboole_0) != (k1_xboole_0))
% 1.37/1.60        | ((k1_mcart_1 @ sk_E_1)
% 1.37/1.60            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 1.37/1.60               (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))))
% 1.37/1.60        | ((sk_A) = (k1_xboole_0))
% 1.37/1.60        | ((sk_B_1) = (k1_xboole_0))
% 1.37/1.60        | ((sk_C_1) = (k1_xboole_0)))),
% 1.37/1.60      inference('sup-', [status(thm)], ['74', '75'])).
% 1.37/1.60  thf('77', plain,
% 1.37/1.60      ((((sk_C_1) = (k1_xboole_0))
% 1.37/1.60        | ((sk_B_1) = (k1_xboole_0))
% 1.37/1.60        | ((sk_A) = (k1_xboole_0))
% 1.37/1.60        | ((k1_mcart_1 @ sk_E_1)
% 1.37/1.60            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 1.37/1.60               (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)))))),
% 1.37/1.60      inference('simplify', [status(thm)], ['76'])).
% 1.37/1.60  thf('78', plain, (((sk_A) != (k1_xboole_0))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('79', plain, (((sk_B_1) != (k1_xboole_0))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('80', plain, (((sk_C_1) != (k1_xboole_0))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('81', plain,
% 1.37/1.60      (((k1_mcart_1 @ sk_E_1)
% 1.37/1.60         = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 1.37/1.60            (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))))),
% 1.37/1.60      inference('simplify_reflect-', [status(thm)], ['77', '78', '79', '80'])).
% 1.37/1.60  thf(d3_mcart_1, axiom,
% 1.37/1.60    (![A:$i,B:$i,C:$i]:
% 1.37/1.60     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 1.37/1.60  thf('82', plain,
% 1.37/1.60      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.37/1.60         ((k3_mcart_1 @ X12 @ X13 @ X14)
% 1.37/1.60           = (k4_tarski @ (k4_tarski @ X12 @ X13) @ X14))),
% 1.37/1.60      inference('cnf', [status(esa)], [d3_mcart_1])).
% 1.37/1.60  thf('83', plain,
% 1.37/1.60      (![X0 : $i]:
% 1.37/1.60         ((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 1.37/1.60           (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ X0)
% 1.37/1.60           = (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ X0))),
% 1.37/1.60      inference('sup+', [status(thm)], ['81', '82'])).
% 1.37/1.60  thf('84', plain,
% 1.37/1.60      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf(dt_k6_mcart_1, axiom,
% 1.37/1.60    (![A:$i,B:$i,C:$i,D:$i]:
% 1.37/1.60     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.37/1.60       ( m1_subset_1 @ ( k6_mcart_1 @ A @ B @ C @ D ) @ B ) ))).
% 1.37/1.60  thf('85', plain,
% 1.37/1.60      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.37/1.60         ((m1_subset_1 @ (k6_mcart_1 @ X18 @ X19 @ X20 @ X21) @ X19)
% 1.37/1.60          | ~ (m1_subset_1 @ X21 @ (k3_zfmisc_1 @ X18 @ X19 @ X20)))),
% 1.37/1.60      inference('cnf', [status(esa)], [dt_k6_mcart_1])).
% 1.37/1.60  thf('86', plain,
% 1.37/1.60      ((m1_subset_1 @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_1) @ sk_B_1)),
% 1.37/1.60      inference('sup-', [status(thm)], ['84', '85'])).
% 1.37/1.60  thf('87', plain,
% 1.37/1.60      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.37/1.60         (~ (m1_subset_1 @ X38 @ sk_B_1)
% 1.37/1.60          | ((sk_D_2) = (X38))
% 1.37/1.60          | ((sk_E_1) != (k3_mcart_1 @ X39 @ X38 @ X40))
% 1.37/1.60          | ~ (m1_subset_1 @ X40 @ sk_C_1)
% 1.37/1.60          | ~ (m1_subset_1 @ X39 @ sk_A))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('88', plain,
% 1.37/1.60      (![X0 : $i, X1 : $i]:
% 1.37/1.60         (~ (m1_subset_1 @ X0 @ sk_A)
% 1.37/1.60          | ~ (m1_subset_1 @ X1 @ sk_C_1)
% 1.37/1.60          | ((sk_E_1)
% 1.37/1.60              != (k3_mcart_1 @ X0 @ 
% 1.37/1.60                  (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_1) @ X1))
% 1.37/1.60          | ((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_1)))),
% 1.37/1.60      inference('sup-', [status(thm)], ['86', '87'])).
% 1.37/1.60  thf('89', plain,
% 1.37/1.60      (((sk_D_2) != (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_1))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('90', plain,
% 1.37/1.60      (![X0 : $i, X1 : $i]:
% 1.37/1.60         (~ (m1_subset_1 @ X0 @ sk_A)
% 1.37/1.60          | ~ (m1_subset_1 @ X1 @ sk_C_1)
% 1.37/1.60          | ((sk_E_1)
% 1.37/1.60              != (k3_mcart_1 @ X0 @ 
% 1.37/1.60                  (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_1) @ X1)))),
% 1.37/1.60      inference('simplify_reflect-', [status(thm)], ['88', '89'])).
% 1.37/1.60  thf('91', plain,
% 1.37/1.60      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf(t50_mcart_1, axiom,
% 1.37/1.60    (![A:$i,B:$i,C:$i]:
% 1.37/1.60     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.37/1.60          ( ( C ) != ( k1_xboole_0 ) ) & 
% 1.37/1.60          ( ~( ![D:$i]:
% 1.37/1.60               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.37/1.60                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 1.37/1.60                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 1.37/1.60                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 1.37/1.60                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 1.37/1.60                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 1.37/1.60  thf('92', plain,
% 1.37/1.60      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.37/1.60         (((X31) = (k1_xboole_0))
% 1.37/1.60          | ((X32) = (k1_xboole_0))
% 1.37/1.60          | ((k6_mcart_1 @ X31 @ X32 @ X34 @ X33)
% 1.37/1.60              = (k2_mcart_1 @ (k1_mcart_1 @ X33)))
% 1.37/1.60          | ~ (m1_subset_1 @ X33 @ (k3_zfmisc_1 @ X31 @ X32 @ X34))
% 1.37/1.60          | ((X34) = (k1_xboole_0)))),
% 1.37/1.60      inference('cnf', [status(esa)], [t50_mcart_1])).
% 1.37/1.60  thf('93', plain,
% 1.37/1.60      ((((sk_C_1) = (k1_xboole_0))
% 1.37/1.60        | ((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_1)
% 1.37/1.60            = (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)))
% 1.37/1.60        | ((sk_B_1) = (k1_xboole_0))
% 1.37/1.60        | ((sk_A) = (k1_xboole_0)))),
% 1.37/1.60      inference('sup-', [status(thm)], ['91', '92'])).
% 1.37/1.60  thf('94', plain, (((sk_A) != (k1_xboole_0))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('95', plain, (((sk_B_1) != (k1_xboole_0))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('96', plain, (((sk_C_1) != (k1_xboole_0))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('97', plain,
% 1.37/1.60      (((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_E_1)
% 1.37/1.60         = (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)))),
% 1.37/1.60      inference('simplify_reflect-', [status(thm)], ['93', '94', '95', '96'])).
% 1.37/1.60  thf('98', plain,
% 1.37/1.60      (![X0 : $i, X1 : $i]:
% 1.37/1.60         (~ (m1_subset_1 @ X0 @ sk_A)
% 1.37/1.60          | ~ (m1_subset_1 @ X1 @ sk_C_1)
% 1.37/1.60          | ((sk_E_1)
% 1.37/1.60              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ X1)))),
% 1.37/1.60      inference('demod', [status(thm)], ['90', '97'])).
% 1.37/1.60  thf('99', plain,
% 1.37/1.60      (![X0 : $i]:
% 1.37/1.60         (((sk_E_1) != (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ X0))
% 1.37/1.60          | ~ (m1_subset_1 @ X0 @ sk_C_1)
% 1.37/1.60          | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A))),
% 1.37/1.60      inference('sup-', [status(thm)], ['83', '98'])).
% 1.37/1.60  thf('100', plain,
% 1.37/1.60      (((r2_hidden @ (k1_mcart_1 @ sk_E_1) @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 1.37/1.60        | ((k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_xboole_0)))),
% 1.37/1.60      inference('sup-', [status(thm)], ['68', '69'])).
% 1.37/1.60  thf('101', plain,
% 1.37/1.60      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.37/1.60         ((r2_hidden @ (k1_mcart_1 @ X22) @ X23)
% 1.37/1.60          | ~ (r2_hidden @ X22 @ (k2_zfmisc_1 @ X23 @ X24)))),
% 1.37/1.60      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.37/1.60  thf('102', plain,
% 1.37/1.60      ((((k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_xboole_0))
% 1.37/1.60        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A))),
% 1.37/1.60      inference('sup-', [status(thm)], ['100', '101'])).
% 1.37/1.60  thf('103', plain,
% 1.37/1.60      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.37/1.60         (((k3_zfmisc_1 @ X27 @ X28 @ X29) != (k1_xboole_0))
% 1.37/1.60          | ((X29) = (k1_xboole_0))
% 1.37/1.60          | ((X28) = (k1_xboole_0))
% 1.37/1.60          | ((X27) = (k1_xboole_0)))),
% 1.37/1.60      inference('cnf', [status(esa)], [t35_mcart_1])).
% 1.37/1.60  thf('104', plain,
% 1.37/1.60      ((((k1_xboole_0) != (k1_xboole_0))
% 1.37/1.60        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A)
% 1.37/1.60        | ((sk_A) = (k1_xboole_0))
% 1.37/1.60        | ((sk_B_1) = (k1_xboole_0))
% 1.37/1.60        | ((sk_C_1) = (k1_xboole_0)))),
% 1.37/1.60      inference('sup-', [status(thm)], ['102', '103'])).
% 1.37/1.60  thf('105', plain,
% 1.37/1.60      ((((sk_C_1) = (k1_xboole_0))
% 1.37/1.60        | ((sk_B_1) = (k1_xboole_0))
% 1.37/1.60        | ((sk_A) = (k1_xboole_0))
% 1.37/1.60        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A))),
% 1.37/1.60      inference('simplify', [status(thm)], ['104'])).
% 1.37/1.60  thf('106', plain, (((sk_A) != (k1_xboole_0))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('107', plain, (((sk_B_1) != (k1_xboole_0))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('108', plain, (((sk_C_1) != (k1_xboole_0))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('109', plain,
% 1.37/1.60      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A)),
% 1.37/1.60      inference('simplify_reflect-', [status(thm)],
% 1.37/1.60                ['105', '106', '107', '108'])).
% 1.37/1.60  thf('110', plain,
% 1.37/1.60      (![X4 : $i, X5 : $i]:
% 1.37/1.60         (~ (r2_hidden @ X4 @ X5)
% 1.37/1.60          | (m1_subset_1 @ X4 @ X5)
% 1.37/1.60          | (v1_xboole_0 @ X5))),
% 1.37/1.60      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.37/1.60  thf('111', plain,
% 1.37/1.60      (((v1_xboole_0 @ sk_A)
% 1.37/1.60        | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A))),
% 1.37/1.60      inference('sup-', [status(thm)], ['109', '110'])).
% 1.37/1.60  thf('112', plain,
% 1.37/1.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.60         (((X2) = (k2_zfmisc_1 @ X1 @ X0))
% 1.37/1.60          | ~ (v1_xboole_0 @ X1)
% 1.37/1.60          | ~ (v1_xboole_0 @ X2))),
% 1.37/1.60      inference('sup+', [status(thm)], ['10', '11'])).
% 1.37/1.60  thf('113', plain, (((sk_A) != (k1_xboole_0))),
% 1.37/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.60  thf('114', plain,
% 1.37/1.60      (![X0 : $i, X1 : $i]:
% 1.37/1.60         (((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0))
% 1.37/1.60          | ~ (v1_xboole_0 @ sk_A)
% 1.37/1.60          | ~ (v1_xboole_0 @ X1))),
% 1.37/1.60      inference('sup-', [status(thm)], ['112', '113'])).
% 1.37/1.60  thf('115', plain,
% 1.37/1.60      (![X0 : $i, X1 : $i]:
% 1.37/1.60         (((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 1.37/1.60      inference('sup+', [status(thm)], ['0', '9'])).
% 1.37/1.60  thf('116', plain,
% 1.37/1.60      (![X1 : $i]: (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ sk_A))),
% 1.37/1.60      inference('clc', [status(thm)], ['114', '115'])).
% 1.37/1.60  thf('117', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.37/1.60      inference('condensation', [status(thm)], ['116'])).
% 1.37/1.60  thf('118', plain,
% 1.37/1.60      ((m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A)),
% 1.37/1.60      inference('clc', [status(thm)], ['111', '117'])).
% 1.37/1.60  thf('119', plain,
% 1.37/1.60      (![X0 : $i]:
% 1.37/1.60         (((sk_E_1) != (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ X0))
% 1.37/1.60          | ~ (m1_subset_1 @ X0 @ sk_C_1))),
% 1.37/1.60      inference('demod', [status(thm)], ['99', '118'])).
% 1.37/1.60  thf('120', plain,
% 1.37/1.60      ((((sk_E_1) != (sk_E_1))
% 1.37/1.60        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E_1) @ sk_C_1))),
% 1.37/1.60      inference('sup-', [status(thm)], ['63', '119'])).
% 1.37/1.60  thf('121', plain, (~ (m1_subset_1 @ (k2_mcart_1 @ sk_E_1) @ sk_C_1)),
% 1.37/1.60      inference('simplify', [status(thm)], ['120'])).
% 1.37/1.60  thf('122', plain, ((v1_xboole_0 @ sk_C_1)),
% 1.37/1.60      inference('sup-', [status(thm)], ['35', '121'])).
% 1.37/1.60  thf('123', plain, ($false), inference('demod', [status(thm)], ['17', '122'])).
% 1.37/1.60  
% 1.37/1.60  % SZS output end Refutation
% 1.37/1.60  
% 1.37/1.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
