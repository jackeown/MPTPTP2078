%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ut7EPMDZLK

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:56 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 370 expanded)
%              Number of leaves         :   37 ( 126 expanded)
%              Depth                    :   22
%              Number of atoms          : 1605 (5501 expanded)
%              Number of equality atoms :  222 ( 765 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 ) ),
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
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ X20 )
      | ( r2_hidden @ X19 @ X20 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 ) )
    | ( r2_hidden @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t23_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( A
          = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X40: $i,X41: $i] :
      ( ( X40
        = ( k4_tarski @ ( k1_mcart_1 @ X40 ) @ ( k2_mcart_1 @ X40 ) ) )
      | ~ ( v1_relat_1 @ X41 )
      | ~ ( r2_hidden @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 ) )
    | ( sk_E_1
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_mcart_1 @ sk_E_1 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( k3_zfmisc_1 @ X30 @ X31 @ X32 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('6',plain,(
    ! [X25: $i,X26: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( v1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 ) )
    | ( sk_E_1
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_mcart_1 @ sk_E_1 ) ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('10',plain,
    ( ( sk_E_1
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_mcart_1 @ sk_E_1 ) ) )
    | ( ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('11',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( k4_zfmisc_1 @ X33 @ X34 @ X35 @ X36 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X33 @ X34 @ X35 ) @ X36 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_E_1
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_mcart_1 @ sk_E_1 ) ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('13',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_zfmisc_1 @ X15 @ X16 )
        = k1_xboole_0 )
      | ( X15 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('14',plain,(
    ! [X16: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X16 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 @ X0 )
        = k1_xboole_0 )
      | ( sk_E_1
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_mcart_1 @ sk_E_1 ) ) ) ) ),
    inference(demod,[status(thm)],['12','14'])).

thf(t55_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 ) )
    <=> ( ( k4_zfmisc_1 @ A @ B @ C @ D )
       != k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( ( k4_zfmisc_1 @ X46 @ X47 @ X48 @ X49 )
       != k1_xboole_0 )
      | ( X49 = k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ( X46 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_E_1
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_mcart_1 @ sk_E_1 ) ) )
      | ( sk_A_1 = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A_1 = k1_xboole_0 )
      | ( sk_E_1
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_mcart_1 @ sk_E_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_E_1
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_mcart_1 @ sk_E_1 ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['18','19','20','21'])).

thf('23',plain,
    ( ( k1_xboole_0 != sk_E_1 )
    | ( sk_E_1
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_mcart_1 @ sk_E_1 ) ) ) ),
    inference(eq_fact,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_E_1
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_mcart_1 @ sk_E_1 ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['18','19','20','21'])).

thf('25',plain,
    ( sk_E_1
    = ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_mcart_1 @ sk_E_1 ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 ) )
    | ( r2_hidden @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('27',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( k3_zfmisc_1 @ X30 @ X31 @ X32 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('28',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X37 ) @ X38 )
      | ~ ( r2_hidden @ X37 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X40: $i,X41: $i] :
      ( ( X40
        = ( k4_tarski @ ( k1_mcart_1 @ X40 ) @ ( k2_mcart_1 @ X40 ) ) )
      | ~ ( v1_relat_1 @ X41 )
      | ~ ( r2_hidden @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('32',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) )
    | ( ( k1_mcart_1 @ sk_E_1 )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X25: $i,X26: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 ) )
    | ( ( k1_mcart_1 @ sk_E_1 )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('36',plain,
    ( ( ( k1_mcart_1 @ sk_E_1 )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ) )
    | ( ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( k4_zfmisc_1 @ X33 @ X34 @ X35 @ X36 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X33 @ X34 @ X35 ) @ X36 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( ( k1_mcart_1 @ sk_E_1 )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X16: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X16 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 @ X0 )
        = k1_xboole_0 )
      | ( ( k1_mcart_1 @ sk_E_1 )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( ( k4_zfmisc_1 @ X46 @ X47 @ X48 @ X49 )
       != k1_xboole_0 )
      | ( X49 = k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ( X46 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k1_mcart_1 @ sk_E_1 )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ) )
      | ( sk_A_1 = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A_1 = k1_xboole_0 )
      | ( ( k1_mcart_1 @ sk_E_1 )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k1_mcart_1 @ sk_E_1 )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['43','44','45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k1_mcart_1 @ sk_E_1 )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['43','44','45','46'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k1_mcart_1 @ sk_E_1 )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ) )
      | ( ( k1_mcart_1 @ sk_E_1 )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_mcart_1 @ sk_E_1 )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ) )
      | ( X1 = X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( k1_mcart_1 @ sk_E_1 )
    = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ) ),
    inference(condensation,[status(thm)],['50'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('52',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k3_mcart_1 @ X27 @ X28 @ X29 )
      = ( k4_tarski @ ( k4_tarski @ X27 @ X28 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ X0 )
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('55',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X37 ) @ X39 )
      | ~ ( r2_hidden @ X37 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('56',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 ) )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('58',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_1 )
    | ( ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( k4_zfmisc_1 @ X33 @ X34 @ X35 @ X36 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X33 @ X34 @ X35 ) @ X36 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X16: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X16 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( ( k4_zfmisc_1 @ X46 @ X47 @ X48 @ X49 )
       != k1_xboole_0 )
      | ( X49 = k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ( X46 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_1 )
      | ( sk_A_1 = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A_1 = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['65','66','67','68'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('70',plain,(
    ! [X23: $i,X24: $i] :
      ( ( m1_subset_1 @ X23 @ X24 )
      | ~ ( r2_hidden @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf(rc1_xboole_0,axiom,(
    ? [A: $i] :
      ( v1_xboole_0 @ A ) )).

thf('72',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('73',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('74',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('75',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['72','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['71','76'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('78',plain,(
    ! [X22: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('79',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X51 @ sk_B_1 )
      | ( sk_E_1
       != ( k3_mcart_1 @ X52 @ X51 @ X53 ) )
      | ( sk_D = X53 )
      | ~ ( m1_subset_1 @ X53 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X52 @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A_1 )
      | ~ ( m1_subset_1 @ X1 @ sk_C_1 )
      | ( sk_D = X1 )
      | ( sk_E_1
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( sk_E_1
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ X0 ) )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A_1 ) ) ),
    inference('sup-',[status(thm)],['53','81'])).

thf('83',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('84',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X37 ) @ X38 )
      | ~ ( r2_hidden @ X37 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('85',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 ) )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('87',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A_1 )
    | ( ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( k4_zfmisc_1 @ X33 @ X34 @ X35 @ X36 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X33 @ X34 @ X35 ) @ X36 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A_1 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X16: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X16 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A_1 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( ( k4_zfmisc_1 @ X46 @ X47 @ X48 @ X49 )
       != k1_xboole_0 )
      | ( X49 = k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ( X46 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A_1 )
      | ( sk_A_1 = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A_1 = k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A_1 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['94','95','96','97'])).

thf('99',plain,(
    ! [X23: $i,X24: $i] :
      ( ( m1_subset_1 @ X23 @ X24 )
      | ~ ( r2_hidden @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A_1 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['72','75'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A_1 ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X22: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('104',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A_1 ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( sk_E_1
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ X0 ) )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['82','104'])).

thf('106',plain,
    ( ( sk_E_1 != sk_E_1 )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C_1 )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['25','105'])).

thf('107',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 ) )
    | ( r2_hidden @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('108',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( k3_zfmisc_1 @ X30 @ X31 @ X32 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('109',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X37 ) @ X39 )
      | ~ ( r2_hidden @ X37 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 ) )
    | ( r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['107','110'])).

thf('112',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('113',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C_1 )
    | ( ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( k3_zfmisc_1 @ X30 @ X31 @ X32 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('115',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X15 @ X14 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['113','116'])).

thf('118',plain,
    ( ( ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X15 @ X14 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('122',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C_1 )
    | ( sk_A_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C_1 ),
    inference('simplify_reflect-',[status(thm)],['123','124','125'])).

thf('127',plain,(
    ! [X23: $i,X24: $i] :
      ( ( m1_subset_1 @ X23 @ X24 )
      | ~ ( r2_hidden @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('128',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,
    ( ( sk_E_1 != sk_E_1 )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['106','128'])).

thf('130',plain,
    ( sk_D
    = ( k2_mcart_1 @ sk_E_1 ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    sk_D
 != ( k7_mcart_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 @ sk_E_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 ) ),
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

thf('133',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( X42 = k1_xboole_0 )
      | ( X43 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X42 @ X43 @ X45 @ X44 )
        = ( k2_mcart_1 @ X44 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k3_zfmisc_1 @ X42 @ X43 @ X45 ) )
      | ( X45 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('134',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 @ sk_E_1 )
      = ( k2_mcart_1 @ sk_E_1 ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( k7_mcart_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 @ sk_E_1 )
    = ( k2_mcart_1 @ sk_E_1 ) ),
    inference('simplify_reflect-',[status(thm)],['134','135','136','137'])).

thf('139',plain,(
    sk_D
 != ( k2_mcart_1 @ sk_E_1 ) ),
    inference(demod,[status(thm)],['131','138'])).

thf('140',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['130','139'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ut7EPMDZLK
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:07:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.69/0.93  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.69/0.93  % Solved by: fo/fo7.sh
% 0.69/0.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.93  % done 886 iterations in 0.480s
% 0.69/0.93  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.69/0.93  % SZS output start Refutation
% 0.69/0.93  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.69/0.93  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.69/0.93  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.69/0.93  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.69/0.93  thf(sk_E_1_type, type, sk_E_1: $i).
% 0.69/0.93  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.69/0.93  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.69/0.93  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.69/0.93  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.69/0.93  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.69/0.93  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.93  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.69/0.93  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.69/0.93  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.69/0.93  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.69/0.93  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.69/0.93  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.69/0.93  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.69/0.93  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.69/0.93  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.69/0.93  thf(sk_D_type, type, sk_D: $i).
% 0.69/0.93  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.69/0.93  thf(t71_mcart_1, conjecture,
% 0.69/0.93    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.69/0.93     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.69/0.93       ( ( ![F:$i]:
% 0.69/0.93           ( ( m1_subset_1 @ F @ A ) =>
% 0.69/0.93             ( ![G:$i]:
% 0.69/0.93               ( ( m1_subset_1 @ G @ B ) =>
% 0.69/0.93                 ( ![H:$i]:
% 0.69/0.93                   ( ( m1_subset_1 @ H @ C ) =>
% 0.69/0.93                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.69/0.93                       ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 0.69/0.93         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.69/0.93           ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.69/0.93           ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 0.69/0.93  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.93    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.69/0.93        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.69/0.93          ( ( ![F:$i]:
% 0.69/0.93              ( ( m1_subset_1 @ F @ A ) =>
% 0.69/0.93                ( ![G:$i]:
% 0.69/0.93                  ( ( m1_subset_1 @ G @ B ) =>
% 0.69/0.93                    ( ![H:$i]:
% 0.69/0.93                      ( ( m1_subset_1 @ H @ C ) =>
% 0.69/0.93                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.69/0.93                          ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 0.69/0.93            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.69/0.93              ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.69/0.93              ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 0.69/0.93    inference('cnf.neg', [status(esa)], [t71_mcart_1])).
% 0.69/0.93  thf('0', plain,
% 0.69/0.93      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1))),
% 0.69/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.93  thf(d2_subset_1, axiom,
% 0.69/0.93    (![A:$i,B:$i]:
% 0.69/0.93     ( ( ( v1_xboole_0 @ A ) =>
% 0.69/0.93         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.69/0.93       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.69/0.93         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.69/0.93  thf('1', plain,
% 0.69/0.93      (![X19 : $i, X20 : $i]:
% 0.69/0.93         (~ (m1_subset_1 @ X19 @ X20)
% 0.69/0.93          | (r2_hidden @ X19 @ X20)
% 0.69/0.93          | (v1_xboole_0 @ X20))),
% 0.69/0.93      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.69/0.93  thf('2', plain,
% 0.69/0.93      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1))
% 0.69/0.93        | (r2_hidden @ sk_E_1 @ (k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1)))),
% 0.69/0.93      inference('sup-', [status(thm)], ['0', '1'])).
% 0.69/0.93  thf(t23_mcart_1, axiom,
% 0.69/0.93    (![A:$i,B:$i]:
% 0.69/0.93     ( ( v1_relat_1 @ B ) =>
% 0.69/0.93       ( ( r2_hidden @ A @ B ) =>
% 0.69/0.93         ( ( A ) = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ))).
% 0.69/0.93  thf('3', plain,
% 0.69/0.93      (![X40 : $i, X41 : $i]:
% 0.69/0.93         (((X40) = (k4_tarski @ (k1_mcart_1 @ X40) @ (k2_mcart_1 @ X40)))
% 0.69/0.93          | ~ (v1_relat_1 @ X41)
% 0.69/0.93          | ~ (r2_hidden @ X40 @ X41))),
% 0.69/0.93      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.69/0.93  thf('4', plain,
% 0.69/0.93      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1))
% 0.69/0.93        | ~ (v1_relat_1 @ (k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1))
% 0.69/0.93        | ((sk_E_1)
% 0.69/0.93            = (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (k2_mcart_1 @ sk_E_1))))),
% 0.69/0.93      inference('sup-', [status(thm)], ['2', '3'])).
% 0.69/0.93  thf(d3_zfmisc_1, axiom,
% 0.69/0.93    (![A:$i,B:$i,C:$i]:
% 0.69/0.93     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.69/0.93       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.69/0.93  thf('5', plain,
% 0.69/0.93      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.69/0.93         ((k3_zfmisc_1 @ X30 @ X31 @ X32)
% 0.69/0.93           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31) @ X32))),
% 0.69/0.93      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.69/0.93  thf(fc6_relat_1, axiom,
% 0.69/0.93    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.69/0.93  thf('6', plain,
% 0.69/0.93      (![X25 : $i, X26 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X25 @ X26))),
% 0.69/0.93      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.69/0.93  thf('7', plain,
% 0.69/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.93         (v1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))),
% 0.69/0.93      inference('sup+', [status(thm)], ['5', '6'])).
% 0.69/0.93  thf('8', plain,
% 0.69/0.93      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1))
% 0.69/0.93        | ((sk_E_1)
% 0.69/0.93            = (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (k2_mcart_1 @ sk_E_1))))),
% 0.69/0.93      inference('demod', [status(thm)], ['4', '7'])).
% 0.69/0.93  thf(l13_xboole_0, axiom,
% 0.69/0.93    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.69/0.93  thf('9', plain,
% 0.69/0.93      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.69/0.93      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.69/0.93  thf('10', plain,
% 0.69/0.93      ((((sk_E_1) = (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (k2_mcart_1 @ sk_E_1)))
% 0.69/0.93        | ((k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.69/0.93      inference('sup-', [status(thm)], ['8', '9'])).
% 0.69/0.93  thf(d4_zfmisc_1, axiom,
% 0.69/0.93    (![A:$i,B:$i,C:$i,D:$i]:
% 0.69/0.93     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.69/0.93       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.69/0.93  thf('11', plain,
% 0.69/0.93      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.69/0.93         ((k4_zfmisc_1 @ X33 @ X34 @ X35 @ X36)
% 0.69/0.93           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X33 @ X34 @ X35) @ X36))),
% 0.69/0.93      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.69/0.93  thf('12', plain,
% 0.69/0.93      (![X0 : $i]:
% 0.69/0.93         (((k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 @ X0)
% 0.69/0.93            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.69/0.93          | ((sk_E_1)
% 0.69/0.93              = (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (k2_mcart_1 @ sk_E_1))))),
% 0.69/0.93      inference('sup+', [status(thm)], ['10', '11'])).
% 0.69/0.93  thf(t113_zfmisc_1, axiom,
% 0.69/0.93    (![A:$i,B:$i]:
% 0.69/0.93     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.69/0.93       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.69/0.93  thf('13', plain,
% 0.69/0.93      (![X15 : $i, X16 : $i]:
% 0.69/0.93         (((k2_zfmisc_1 @ X15 @ X16) = (k1_xboole_0))
% 0.69/0.93          | ((X15) != (k1_xboole_0)))),
% 0.69/0.93      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.69/0.93  thf('14', plain,
% 0.69/0.93      (![X16 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X16) = (k1_xboole_0))),
% 0.69/0.93      inference('simplify', [status(thm)], ['13'])).
% 0.69/0.93  thf('15', plain,
% 0.69/0.93      (![X0 : $i]:
% 0.69/0.93         (((k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 @ X0) = (k1_xboole_0))
% 0.69/0.93          | ((sk_E_1)
% 0.69/0.93              = (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (k2_mcart_1 @ sk_E_1))))),
% 0.69/0.93      inference('demod', [status(thm)], ['12', '14'])).
% 0.69/0.93  thf(t55_mcart_1, axiom,
% 0.69/0.93    (![A:$i,B:$i,C:$i,D:$i]:
% 0.69/0.93     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.69/0.93         ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) ) <=>
% 0.69/0.93       ( ( k4_zfmisc_1 @ A @ B @ C @ D ) != ( k1_xboole_0 ) ) ))).
% 0.69/0.93  thf('16', plain,
% 0.69/0.93      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.69/0.93         (((k4_zfmisc_1 @ X46 @ X47 @ X48 @ X49) != (k1_xboole_0))
% 0.69/0.93          | ((X49) = (k1_xboole_0))
% 0.69/0.93          | ((X48) = (k1_xboole_0))
% 0.69/0.93          | ((X47) = (k1_xboole_0))
% 0.69/0.93          | ((X46) = (k1_xboole_0)))),
% 0.69/0.93      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.69/0.93  thf('17', plain,
% 0.69/0.93      (![X0 : $i]:
% 0.69/0.93         (((k1_xboole_0) != (k1_xboole_0))
% 0.69/0.93          | ((sk_E_1)
% 0.69/0.93              = (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (k2_mcart_1 @ sk_E_1)))
% 0.69/0.93          | ((sk_A_1) = (k1_xboole_0))
% 0.69/0.93          | ((sk_B_1) = (k1_xboole_0))
% 0.69/0.93          | ((sk_C_1) = (k1_xboole_0))
% 0.69/0.93          | ((X0) = (k1_xboole_0)))),
% 0.69/0.93      inference('sup-', [status(thm)], ['15', '16'])).
% 0.69/0.93  thf('18', plain,
% 0.69/0.93      (![X0 : $i]:
% 0.69/0.93         (((X0) = (k1_xboole_0))
% 0.69/0.93          | ((sk_C_1) = (k1_xboole_0))
% 0.69/0.93          | ((sk_B_1) = (k1_xboole_0))
% 0.69/0.93          | ((sk_A_1) = (k1_xboole_0))
% 0.69/0.93          | ((sk_E_1)
% 0.69/0.93              = (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (k2_mcart_1 @ sk_E_1))))),
% 0.69/0.93      inference('simplify', [status(thm)], ['17'])).
% 0.69/0.93  thf('19', plain, (((sk_A_1) != (k1_xboole_0))),
% 0.69/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.93  thf('20', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.69/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.93  thf('21', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.69/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.93  thf('22', plain,
% 0.69/0.93      (![X0 : $i]:
% 0.69/0.93         (((X0) = (k1_xboole_0))
% 0.69/0.93          | ((sk_E_1)
% 0.69/0.93              = (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (k2_mcart_1 @ sk_E_1))))),
% 0.69/0.93      inference('simplify_reflect-', [status(thm)], ['18', '19', '20', '21'])).
% 0.69/0.93  thf('23', plain,
% 0.69/0.93      ((((k1_xboole_0) != (sk_E_1))
% 0.69/0.93        | ((sk_E_1)
% 0.69/0.93            = (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (k2_mcart_1 @ sk_E_1))))),
% 0.69/0.93      inference('eq_fact', [status(thm)], ['22'])).
% 0.69/0.93  thf('24', plain,
% 0.69/0.93      (![X0 : $i]:
% 0.69/0.93         (((X0) = (k1_xboole_0))
% 0.69/0.93          | ((sk_E_1)
% 0.69/0.93              = (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (k2_mcart_1 @ sk_E_1))))),
% 0.69/0.93      inference('simplify_reflect-', [status(thm)], ['18', '19', '20', '21'])).
% 0.69/0.93  thf('25', plain,
% 0.69/0.93      (((sk_E_1) = (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (k2_mcart_1 @ sk_E_1)))),
% 0.69/0.93      inference('clc', [status(thm)], ['23', '24'])).
% 0.69/0.93  thf('26', plain,
% 0.69/0.93      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1))
% 0.69/0.93        | (r2_hidden @ sk_E_1 @ (k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1)))),
% 0.69/0.93      inference('sup-', [status(thm)], ['0', '1'])).
% 0.69/0.93  thf('27', plain,
% 0.69/0.93      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.69/0.93         ((k3_zfmisc_1 @ X30 @ X31 @ X32)
% 0.69/0.93           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31) @ X32))),
% 0.69/0.93      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.69/0.93  thf(t10_mcart_1, axiom,
% 0.69/0.93    (![A:$i,B:$i,C:$i]:
% 0.69/0.93     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.69/0.93       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.69/0.93         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.69/0.93  thf('28', plain,
% 0.69/0.93      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.69/0.93         ((r2_hidden @ (k1_mcart_1 @ X37) @ X38)
% 0.69/0.93          | ~ (r2_hidden @ X37 @ (k2_zfmisc_1 @ X38 @ X39)))),
% 0.69/0.93      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.69/0.93  thf('29', plain,
% 0.69/0.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.69/0.93         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.69/0.93          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.69/0.93      inference('sup-', [status(thm)], ['27', '28'])).
% 0.69/0.93  thf('30', plain,
% 0.69/0.93      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1))
% 0.69/0.93        | (r2_hidden @ (k1_mcart_1 @ sk_E_1) @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 0.69/0.93      inference('sup-', [status(thm)], ['26', '29'])).
% 0.69/0.93  thf('31', plain,
% 0.69/0.93      (![X40 : $i, X41 : $i]:
% 0.69/0.93         (((X40) = (k4_tarski @ (k1_mcart_1 @ X40) @ (k2_mcart_1 @ X40)))
% 0.69/0.93          | ~ (v1_relat_1 @ X41)
% 0.69/0.93          | ~ (r2_hidden @ X40 @ X41))),
% 0.69/0.93      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.69/0.93  thf('32', plain,
% 0.69/0.93      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1))
% 0.69/0.93        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1))
% 0.69/0.93        | ((k1_mcart_1 @ sk_E_1)
% 0.69/0.93            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 0.69/0.93               (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)))))),
% 0.69/0.93      inference('sup-', [status(thm)], ['30', '31'])).
% 0.69/0.93  thf('33', plain,
% 0.69/0.93      (![X25 : $i, X26 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X25 @ X26))),
% 0.69/0.93      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.69/0.93  thf('34', plain,
% 0.69/0.93      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1))
% 0.69/0.93        | ((k1_mcart_1 @ sk_E_1)
% 0.69/0.93            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 0.69/0.93               (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)))))),
% 0.69/0.93      inference('demod', [status(thm)], ['32', '33'])).
% 0.69/0.93  thf('35', plain,
% 0.69/0.93      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.69/0.93      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.69/0.93  thf('36', plain,
% 0.69/0.93      ((((k1_mcart_1 @ sk_E_1)
% 0.69/0.93          = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 0.69/0.93             (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))))
% 0.69/0.93        | ((k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.69/0.93      inference('sup-', [status(thm)], ['34', '35'])).
% 0.69/0.93  thf('37', plain,
% 0.69/0.93      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.69/0.93         ((k4_zfmisc_1 @ X33 @ X34 @ X35 @ X36)
% 0.69/0.93           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X33 @ X34 @ X35) @ X36))),
% 0.69/0.93      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.69/0.93  thf('38', plain,
% 0.69/0.93      (![X0 : $i]:
% 0.69/0.93         (((k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 @ X0)
% 0.69/0.93            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.69/0.93          | ((k1_mcart_1 @ sk_E_1)
% 0.69/0.93              = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 0.69/0.93                 (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)))))),
% 0.69/0.93      inference('sup+', [status(thm)], ['36', '37'])).
% 0.69/0.93  thf('39', plain,
% 0.69/0.93      (![X16 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X16) = (k1_xboole_0))),
% 0.69/0.93      inference('simplify', [status(thm)], ['13'])).
% 0.69/0.93  thf('40', plain,
% 0.69/0.93      (![X0 : $i]:
% 0.69/0.93         (((k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 @ X0) = (k1_xboole_0))
% 0.69/0.93          | ((k1_mcart_1 @ sk_E_1)
% 0.69/0.93              = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 0.69/0.93                 (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)))))),
% 0.69/0.93      inference('demod', [status(thm)], ['38', '39'])).
% 0.69/0.93  thf('41', plain,
% 0.69/0.93      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.69/0.93         (((k4_zfmisc_1 @ X46 @ X47 @ X48 @ X49) != (k1_xboole_0))
% 0.69/0.93          | ((X49) = (k1_xboole_0))
% 0.69/0.93          | ((X48) = (k1_xboole_0))
% 0.69/0.93          | ((X47) = (k1_xboole_0))
% 0.69/0.93          | ((X46) = (k1_xboole_0)))),
% 0.69/0.93      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.69/0.93  thf('42', plain,
% 0.69/0.93      (![X0 : $i]:
% 0.69/0.93         (((k1_xboole_0) != (k1_xboole_0))
% 0.69/0.93          | ((k1_mcart_1 @ sk_E_1)
% 0.69/0.93              = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 0.69/0.93                 (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))))
% 0.69/0.93          | ((sk_A_1) = (k1_xboole_0))
% 0.69/0.93          | ((sk_B_1) = (k1_xboole_0))
% 0.69/0.93          | ((sk_C_1) = (k1_xboole_0))
% 0.69/0.93          | ((X0) = (k1_xboole_0)))),
% 0.69/0.93      inference('sup-', [status(thm)], ['40', '41'])).
% 0.69/0.93  thf('43', plain,
% 0.69/0.93      (![X0 : $i]:
% 0.69/0.93         (((X0) = (k1_xboole_0))
% 0.69/0.93          | ((sk_C_1) = (k1_xboole_0))
% 0.69/0.93          | ((sk_B_1) = (k1_xboole_0))
% 0.69/0.93          | ((sk_A_1) = (k1_xboole_0))
% 0.69/0.93          | ((k1_mcart_1 @ sk_E_1)
% 0.69/0.93              = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 0.69/0.93                 (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)))))),
% 0.69/0.93      inference('simplify', [status(thm)], ['42'])).
% 0.69/0.93  thf('44', plain, (((sk_A_1) != (k1_xboole_0))),
% 0.69/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.93  thf('45', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.69/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.93  thf('46', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.69/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.93  thf('47', plain,
% 0.69/0.93      (![X0 : $i]:
% 0.69/0.93         (((X0) = (k1_xboole_0))
% 0.69/0.93          | ((k1_mcart_1 @ sk_E_1)
% 0.69/0.93              = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 0.69/0.93                 (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)))))),
% 0.69/0.93      inference('simplify_reflect-', [status(thm)], ['43', '44', '45', '46'])).
% 0.69/0.93  thf('48', plain,
% 0.69/0.93      (![X0 : $i]:
% 0.69/0.93         (((X0) = (k1_xboole_0))
% 0.69/0.93          | ((k1_mcart_1 @ sk_E_1)
% 0.69/0.93              = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 0.69/0.93                 (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)))))),
% 0.69/0.93      inference('simplify_reflect-', [status(thm)], ['43', '44', '45', '46'])).
% 0.69/0.93  thf('49', plain,
% 0.69/0.93      (![X0 : $i, X1 : $i]:
% 0.69/0.93         (((X1) = (X0))
% 0.69/0.93          | ((k1_mcart_1 @ sk_E_1)
% 0.69/0.93              = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 0.69/0.94                 (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))))
% 0.69/0.94          | ((k1_mcart_1 @ sk_E_1)
% 0.69/0.94              = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 0.69/0.94                 (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)))))),
% 0.69/0.94      inference('sup+', [status(thm)], ['47', '48'])).
% 0.69/0.94  thf('50', plain,
% 0.69/0.94      (![X0 : $i, X1 : $i]:
% 0.69/0.94         (((k1_mcart_1 @ sk_E_1)
% 0.69/0.94            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 0.69/0.94               (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))))
% 0.69/0.94          | ((X1) = (X0)))),
% 0.69/0.94      inference('simplify', [status(thm)], ['49'])).
% 0.69/0.94  thf('51', plain,
% 0.69/0.94      (((k1_mcart_1 @ sk_E_1)
% 0.69/0.94         = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 0.69/0.94            (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))))),
% 0.69/0.94      inference('condensation', [status(thm)], ['50'])).
% 0.69/0.94  thf(d3_mcart_1, axiom,
% 0.69/0.94    (![A:$i,B:$i,C:$i]:
% 0.69/0.94     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.69/0.94  thf('52', plain,
% 0.69/0.94      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.69/0.94         ((k3_mcart_1 @ X27 @ X28 @ X29)
% 0.69/0.94           = (k4_tarski @ (k4_tarski @ X27 @ X28) @ X29))),
% 0.69/0.94      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.69/0.94  thf('53', plain,
% 0.69/0.94      (![X0 : $i]:
% 0.69/0.94         ((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 0.69/0.94           (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ X0)
% 0.69/0.94           = (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ X0))),
% 0.69/0.94      inference('sup+', [status(thm)], ['51', '52'])).
% 0.69/0.94  thf('54', plain,
% 0.69/0.94      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1))
% 0.69/0.94        | (r2_hidden @ (k1_mcart_1 @ sk_E_1) @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 0.69/0.94      inference('sup-', [status(thm)], ['26', '29'])).
% 0.69/0.94  thf('55', plain,
% 0.69/0.94      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.69/0.94         ((r2_hidden @ (k2_mcart_1 @ X37) @ X39)
% 0.69/0.94          | ~ (r2_hidden @ X37 @ (k2_zfmisc_1 @ X38 @ X39)))),
% 0.69/0.94      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.69/0.94  thf('56', plain,
% 0.69/0.94      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1))
% 0.69/0.94        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_1))),
% 0.69/0.94      inference('sup-', [status(thm)], ['54', '55'])).
% 0.69/0.94  thf('57', plain,
% 0.69/0.94      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.69/0.94      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.69/0.94  thf('58', plain,
% 0.69/0.94      (((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_1)
% 0.69/0.94        | ((k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.69/0.94      inference('sup-', [status(thm)], ['56', '57'])).
% 0.69/0.94  thf('59', plain,
% 0.69/0.94      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.69/0.94         ((k4_zfmisc_1 @ X33 @ X34 @ X35 @ X36)
% 0.69/0.94           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X33 @ X34 @ X35) @ X36))),
% 0.69/0.94      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.69/0.94  thf('60', plain,
% 0.69/0.94      (![X0 : $i]:
% 0.69/0.94         (((k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 @ X0)
% 0.69/0.94            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.69/0.94          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_1))),
% 0.69/0.94      inference('sup+', [status(thm)], ['58', '59'])).
% 0.69/0.94  thf('61', plain,
% 0.69/0.94      (![X16 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X16) = (k1_xboole_0))),
% 0.69/0.94      inference('simplify', [status(thm)], ['13'])).
% 0.69/0.94  thf('62', plain,
% 0.69/0.94      (![X0 : $i]:
% 0.69/0.94         (((k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 @ X0) = (k1_xboole_0))
% 0.69/0.94          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_1))),
% 0.69/0.94      inference('demod', [status(thm)], ['60', '61'])).
% 0.69/0.94  thf('63', plain,
% 0.69/0.94      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.69/0.94         (((k4_zfmisc_1 @ X46 @ X47 @ X48 @ X49) != (k1_xboole_0))
% 0.69/0.94          | ((X49) = (k1_xboole_0))
% 0.69/0.94          | ((X48) = (k1_xboole_0))
% 0.69/0.94          | ((X47) = (k1_xboole_0))
% 0.69/0.94          | ((X46) = (k1_xboole_0)))),
% 0.69/0.94      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.69/0.94  thf('64', plain,
% 0.69/0.94      (![X0 : $i]:
% 0.69/0.94         (((k1_xboole_0) != (k1_xboole_0))
% 0.69/0.94          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_1)
% 0.69/0.94          | ((sk_A_1) = (k1_xboole_0))
% 0.69/0.94          | ((sk_B_1) = (k1_xboole_0))
% 0.69/0.94          | ((sk_C_1) = (k1_xboole_0))
% 0.69/0.94          | ((X0) = (k1_xboole_0)))),
% 0.69/0.94      inference('sup-', [status(thm)], ['62', '63'])).
% 0.69/0.94  thf('65', plain,
% 0.69/0.94      (![X0 : $i]:
% 0.69/0.94         (((X0) = (k1_xboole_0))
% 0.69/0.94          | ((sk_C_1) = (k1_xboole_0))
% 0.69/0.94          | ((sk_B_1) = (k1_xboole_0))
% 0.69/0.94          | ((sk_A_1) = (k1_xboole_0))
% 0.69/0.94          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_1))),
% 0.69/0.94      inference('simplify', [status(thm)], ['64'])).
% 0.69/0.94  thf('66', plain, (((sk_A_1) != (k1_xboole_0))),
% 0.69/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.94  thf('67', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.69/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.94  thf('68', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.69/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.94  thf('69', plain,
% 0.69/0.94      (![X0 : $i]:
% 0.69/0.94         (((X0) = (k1_xboole_0))
% 0.69/0.94          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_1))),
% 0.69/0.94      inference('simplify_reflect-', [status(thm)], ['65', '66', '67', '68'])).
% 0.69/0.94  thf(t1_subset, axiom,
% 0.69/0.94    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.69/0.94  thf('70', plain,
% 0.69/0.94      (![X23 : $i, X24 : $i]:
% 0.69/0.94         ((m1_subset_1 @ X23 @ X24) | ~ (r2_hidden @ X23 @ X24))),
% 0.69/0.94      inference('cnf', [status(esa)], [t1_subset])).
% 0.69/0.94  thf('71', plain,
% 0.69/0.94      (![X0 : $i]:
% 0.69/0.94         (((X0) = (k1_xboole_0))
% 0.69/0.94          | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_1))),
% 0.69/0.94      inference('sup-', [status(thm)], ['69', '70'])).
% 0.69/0.94  thf(rc1_xboole_0, axiom, (?[A:$i]: ( v1_xboole_0 @ A ))).
% 0.69/0.94  thf('72', plain, ((v1_xboole_0 @ sk_A)),
% 0.69/0.94      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.69/0.94  thf('73', plain, ((v1_xboole_0 @ sk_A)),
% 0.69/0.94      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.69/0.94  thf('74', plain,
% 0.69/0.94      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.69/0.94      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.69/0.94  thf('75', plain, (((sk_A) = (k1_xboole_0))),
% 0.69/0.94      inference('sup-', [status(thm)], ['73', '74'])).
% 0.69/0.94  thf('76', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.69/0.94      inference('demod', [status(thm)], ['72', '75'])).
% 0.69/0.94  thf('77', plain,
% 0.69/0.94      (![X0 : $i]:
% 0.69/0.94         ((v1_xboole_0 @ X0)
% 0.69/0.94          | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_1))),
% 0.69/0.94      inference('sup+', [status(thm)], ['71', '76'])).
% 0.69/0.94  thf(fc1_subset_1, axiom,
% 0.69/0.94    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.69/0.94  thf('78', plain, (![X22 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X22))),
% 0.69/0.94      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.69/0.94  thf('79', plain,
% 0.69/0.94      ((m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_1)),
% 0.69/0.94      inference('sup-', [status(thm)], ['77', '78'])).
% 0.69/0.94  thf('80', plain,
% 0.69/0.94      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.69/0.94         (~ (m1_subset_1 @ X51 @ sk_B_1)
% 0.69/0.94          | ((sk_E_1) != (k3_mcart_1 @ X52 @ X51 @ X53))
% 0.69/0.94          | ((sk_D) = (X53))
% 0.69/0.94          | ~ (m1_subset_1 @ X53 @ sk_C_1)
% 0.69/0.94          | ~ (m1_subset_1 @ X52 @ sk_A_1))),
% 0.69/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.94  thf('81', plain,
% 0.69/0.94      (![X0 : $i, X1 : $i]:
% 0.69/0.94         (~ (m1_subset_1 @ X0 @ sk_A_1)
% 0.69/0.94          | ~ (m1_subset_1 @ X1 @ sk_C_1)
% 0.69/0.94          | ((sk_D) = (X1))
% 0.69/0.94          | ((sk_E_1)
% 0.69/0.94              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ X1)))),
% 0.69/0.94      inference('sup-', [status(thm)], ['79', '80'])).
% 0.69/0.94  thf('82', plain,
% 0.69/0.94      (![X0 : $i]:
% 0.69/0.94         (((sk_E_1) != (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ X0))
% 0.69/0.94          | ((sk_D) = (X0))
% 0.69/0.94          | ~ (m1_subset_1 @ X0 @ sk_C_1)
% 0.69/0.94          | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A_1))),
% 0.69/0.94      inference('sup-', [status(thm)], ['53', '81'])).
% 0.69/0.94  thf('83', plain,
% 0.69/0.94      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1))
% 0.69/0.94        | (r2_hidden @ (k1_mcart_1 @ sk_E_1) @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 0.69/0.94      inference('sup-', [status(thm)], ['26', '29'])).
% 0.69/0.94  thf('84', plain,
% 0.69/0.94      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.69/0.94         ((r2_hidden @ (k1_mcart_1 @ X37) @ X38)
% 0.69/0.94          | ~ (r2_hidden @ X37 @ (k2_zfmisc_1 @ X38 @ X39)))),
% 0.69/0.94      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.69/0.94  thf('85', plain,
% 0.69/0.94      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1))
% 0.69/0.94        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A_1))),
% 0.69/0.94      inference('sup-', [status(thm)], ['83', '84'])).
% 0.69/0.94  thf('86', plain,
% 0.69/0.94      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.69/0.94      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.69/0.94  thf('87', plain,
% 0.69/0.94      (((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A_1)
% 0.69/0.94        | ((k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.69/0.94      inference('sup-', [status(thm)], ['85', '86'])).
% 0.69/0.94  thf('88', plain,
% 0.69/0.94      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.69/0.94         ((k4_zfmisc_1 @ X33 @ X34 @ X35 @ X36)
% 0.69/0.94           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X33 @ X34 @ X35) @ X36))),
% 0.69/0.94      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.69/0.94  thf('89', plain,
% 0.69/0.94      (![X0 : $i]:
% 0.69/0.94         (((k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 @ X0)
% 0.69/0.94            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.69/0.94          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A_1))),
% 0.69/0.94      inference('sup+', [status(thm)], ['87', '88'])).
% 0.69/0.94  thf('90', plain,
% 0.69/0.94      (![X16 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X16) = (k1_xboole_0))),
% 0.69/0.94      inference('simplify', [status(thm)], ['13'])).
% 0.69/0.94  thf('91', plain,
% 0.69/0.94      (![X0 : $i]:
% 0.69/0.94         (((k4_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 @ X0) = (k1_xboole_0))
% 0.69/0.94          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A_1))),
% 0.69/0.94      inference('demod', [status(thm)], ['89', '90'])).
% 0.69/0.94  thf('92', plain,
% 0.69/0.94      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.69/0.94         (((k4_zfmisc_1 @ X46 @ X47 @ X48 @ X49) != (k1_xboole_0))
% 0.69/0.94          | ((X49) = (k1_xboole_0))
% 0.69/0.94          | ((X48) = (k1_xboole_0))
% 0.69/0.94          | ((X47) = (k1_xboole_0))
% 0.69/0.94          | ((X46) = (k1_xboole_0)))),
% 0.69/0.94      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.69/0.94  thf('93', plain,
% 0.69/0.94      (![X0 : $i]:
% 0.69/0.94         (((k1_xboole_0) != (k1_xboole_0))
% 0.69/0.94          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A_1)
% 0.69/0.94          | ((sk_A_1) = (k1_xboole_0))
% 0.69/0.94          | ((sk_B_1) = (k1_xboole_0))
% 0.69/0.94          | ((sk_C_1) = (k1_xboole_0))
% 0.69/0.94          | ((X0) = (k1_xboole_0)))),
% 0.69/0.94      inference('sup-', [status(thm)], ['91', '92'])).
% 0.69/0.94  thf('94', plain,
% 0.69/0.94      (![X0 : $i]:
% 0.69/0.94         (((X0) = (k1_xboole_0))
% 0.69/0.94          | ((sk_C_1) = (k1_xboole_0))
% 0.69/0.94          | ((sk_B_1) = (k1_xboole_0))
% 0.69/0.94          | ((sk_A_1) = (k1_xboole_0))
% 0.69/0.94          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A_1))),
% 0.69/0.94      inference('simplify', [status(thm)], ['93'])).
% 0.69/0.94  thf('95', plain, (((sk_A_1) != (k1_xboole_0))),
% 0.69/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.94  thf('96', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.69/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.94  thf('97', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.69/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.94  thf('98', plain,
% 0.69/0.94      (![X0 : $i]:
% 0.69/0.94         (((X0) = (k1_xboole_0))
% 0.69/0.94          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A_1))),
% 0.69/0.94      inference('simplify_reflect-', [status(thm)], ['94', '95', '96', '97'])).
% 0.69/0.94  thf('99', plain,
% 0.69/0.94      (![X23 : $i, X24 : $i]:
% 0.69/0.94         ((m1_subset_1 @ X23 @ X24) | ~ (r2_hidden @ X23 @ X24))),
% 0.69/0.94      inference('cnf', [status(esa)], [t1_subset])).
% 0.69/0.94  thf('100', plain,
% 0.69/0.94      (![X0 : $i]:
% 0.69/0.94         (((X0) = (k1_xboole_0))
% 0.69/0.94          | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A_1))),
% 0.69/0.94      inference('sup-', [status(thm)], ['98', '99'])).
% 0.69/0.94  thf('101', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.69/0.94      inference('demod', [status(thm)], ['72', '75'])).
% 0.69/0.94  thf('102', plain,
% 0.69/0.94      (![X0 : $i]:
% 0.69/0.94         ((v1_xboole_0 @ X0)
% 0.69/0.94          | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A_1))),
% 0.69/0.94      inference('sup+', [status(thm)], ['100', '101'])).
% 0.69/0.94  thf('103', plain, (![X22 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X22))),
% 0.69/0.94      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.69/0.94  thf('104', plain,
% 0.69/0.94      ((m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A_1)),
% 0.69/0.94      inference('sup-', [status(thm)], ['102', '103'])).
% 0.69/0.94  thf('105', plain,
% 0.69/0.94      (![X0 : $i]:
% 0.69/0.94         (((sk_E_1) != (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ X0))
% 0.69/0.94          | ((sk_D) = (X0))
% 0.69/0.94          | ~ (m1_subset_1 @ X0 @ sk_C_1))),
% 0.69/0.94      inference('demod', [status(thm)], ['82', '104'])).
% 0.69/0.94  thf('106', plain,
% 0.69/0.94      ((((sk_E_1) != (sk_E_1))
% 0.69/0.94        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E_1) @ sk_C_1)
% 0.69/0.94        | ((sk_D) = (k2_mcart_1 @ sk_E_1)))),
% 0.69/0.94      inference('sup-', [status(thm)], ['25', '105'])).
% 0.69/0.94  thf('107', plain,
% 0.69/0.94      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1))
% 0.69/0.94        | (r2_hidden @ sk_E_1 @ (k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1)))),
% 0.69/0.94      inference('sup-', [status(thm)], ['0', '1'])).
% 0.69/0.94  thf('108', plain,
% 0.69/0.94      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.69/0.94         ((k3_zfmisc_1 @ X30 @ X31 @ X32)
% 0.69/0.94           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31) @ X32))),
% 0.69/0.94      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.69/0.94  thf('109', plain,
% 0.69/0.94      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.69/0.94         ((r2_hidden @ (k2_mcart_1 @ X37) @ X39)
% 0.69/0.94          | ~ (r2_hidden @ X37 @ (k2_zfmisc_1 @ X38 @ X39)))),
% 0.69/0.94      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.69/0.94  thf('110', plain,
% 0.69/0.94      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.69/0.94         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.69/0.94          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 0.69/0.94      inference('sup-', [status(thm)], ['108', '109'])).
% 0.69/0.94  thf('111', plain,
% 0.69/0.94      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1))
% 0.69/0.94        | (r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C_1))),
% 0.69/0.94      inference('sup-', [status(thm)], ['107', '110'])).
% 0.69/0.94  thf('112', plain,
% 0.69/0.94      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.69/0.94      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.69/0.94  thf('113', plain,
% 0.69/0.94      (((r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C_1)
% 0.69/0.94        | ((k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.69/0.94      inference('sup-', [status(thm)], ['111', '112'])).
% 0.69/0.94  thf('114', plain,
% 0.69/0.94      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.69/0.94         ((k3_zfmisc_1 @ X30 @ X31 @ X32)
% 0.69/0.94           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31) @ X32))),
% 0.69/0.94      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.69/0.94  thf('115', plain,
% 0.69/0.94      (![X14 : $i, X15 : $i]:
% 0.69/0.94         (((X14) = (k1_xboole_0))
% 0.69/0.94          | ((X15) = (k1_xboole_0))
% 0.69/0.94          | ((k2_zfmisc_1 @ X15 @ X14) != (k1_xboole_0)))),
% 0.69/0.94      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.69/0.94  thf('116', plain,
% 0.69/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.94         (((k3_zfmisc_1 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 0.69/0.94          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 0.69/0.94          | ((X0) = (k1_xboole_0)))),
% 0.69/0.94      inference('sup-', [status(thm)], ['114', '115'])).
% 0.69/0.94  thf('117', plain,
% 0.69/0.94      ((((k1_xboole_0) != (k1_xboole_0))
% 0.69/0.94        | (r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C_1)
% 0.69/0.94        | ((sk_C_1) = (k1_xboole_0))
% 0.69/0.94        | ((k2_zfmisc_1 @ sk_A_1 @ sk_B_1) = (k1_xboole_0)))),
% 0.69/0.94      inference('sup-', [status(thm)], ['113', '116'])).
% 0.69/0.94  thf('118', plain,
% 0.69/0.94      ((((k2_zfmisc_1 @ sk_A_1 @ sk_B_1) = (k1_xboole_0))
% 0.69/0.94        | ((sk_C_1) = (k1_xboole_0))
% 0.69/0.94        | (r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C_1))),
% 0.69/0.94      inference('simplify', [status(thm)], ['117'])).
% 0.69/0.94  thf('119', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.69/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.94  thf('120', plain,
% 0.69/0.94      ((((k2_zfmisc_1 @ sk_A_1 @ sk_B_1) = (k1_xboole_0))
% 0.69/0.94        | (r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C_1))),
% 0.69/0.94      inference('simplify_reflect-', [status(thm)], ['118', '119'])).
% 0.69/0.94  thf('121', plain,
% 0.69/0.94      (![X14 : $i, X15 : $i]:
% 0.69/0.94         (((X14) = (k1_xboole_0))
% 0.69/0.94          | ((X15) = (k1_xboole_0))
% 0.69/0.94          | ((k2_zfmisc_1 @ X15 @ X14) != (k1_xboole_0)))),
% 0.69/0.94      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.69/0.94  thf('122', plain,
% 0.69/0.94      ((((k1_xboole_0) != (k1_xboole_0))
% 0.69/0.94        | (r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C_1)
% 0.69/0.94        | ((sk_A_1) = (k1_xboole_0))
% 0.69/0.94        | ((sk_B_1) = (k1_xboole_0)))),
% 0.69/0.94      inference('sup-', [status(thm)], ['120', '121'])).
% 0.69/0.94  thf('123', plain,
% 0.69/0.94      ((((sk_B_1) = (k1_xboole_0))
% 0.69/0.94        | ((sk_A_1) = (k1_xboole_0))
% 0.69/0.94        | (r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C_1))),
% 0.69/0.94      inference('simplify', [status(thm)], ['122'])).
% 0.69/0.94  thf('124', plain, (((sk_A_1) != (k1_xboole_0))),
% 0.69/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.94  thf('125', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.69/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.94  thf('126', plain, ((r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C_1)),
% 0.69/0.94      inference('simplify_reflect-', [status(thm)], ['123', '124', '125'])).
% 0.69/0.94  thf('127', plain,
% 0.69/0.94      (![X23 : $i, X24 : $i]:
% 0.69/0.94         ((m1_subset_1 @ X23 @ X24) | ~ (r2_hidden @ X23 @ X24))),
% 0.69/0.94      inference('cnf', [status(esa)], [t1_subset])).
% 0.69/0.94  thf('128', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_E_1) @ sk_C_1)),
% 0.69/0.94      inference('sup-', [status(thm)], ['126', '127'])).
% 0.69/0.94  thf('129', plain,
% 0.69/0.94      ((((sk_E_1) != (sk_E_1)) | ((sk_D) = (k2_mcart_1 @ sk_E_1)))),
% 0.69/0.94      inference('demod', [status(thm)], ['106', '128'])).
% 0.69/0.94  thf('130', plain, (((sk_D) = (k2_mcart_1 @ sk_E_1))),
% 0.69/0.94      inference('simplify', [status(thm)], ['129'])).
% 0.69/0.94  thf('131', plain,
% 0.69/0.94      (((sk_D) != (k7_mcart_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 @ sk_E_1))),
% 0.69/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.94  thf('132', plain,
% 0.69/0.94      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A_1 @ sk_B_1 @ sk_C_1))),
% 0.69/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.94  thf(t50_mcart_1, axiom,
% 0.69/0.94    (![A:$i,B:$i,C:$i]:
% 0.69/0.94     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.69/0.94          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.69/0.94          ( ~( ![D:$i]:
% 0.69/0.94               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.69/0.94                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.69/0.94                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.69/0.94                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.69/0.94                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.69/0.94                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.69/0.94  thf('133', plain,
% 0.69/0.94      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.69/0.94         (((X42) = (k1_xboole_0))
% 0.69/0.94          | ((X43) = (k1_xboole_0))
% 0.69/0.94          | ((k7_mcart_1 @ X42 @ X43 @ X45 @ X44) = (k2_mcart_1 @ X44))
% 0.69/0.94          | ~ (m1_subset_1 @ X44 @ (k3_zfmisc_1 @ X42 @ X43 @ X45))
% 0.69/0.94          | ((X45) = (k1_xboole_0)))),
% 0.69/0.94      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.69/0.94  thf('134', plain,
% 0.69/0.94      ((((sk_C_1) = (k1_xboole_0))
% 0.69/0.94        | ((k7_mcart_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 @ sk_E_1)
% 0.69/0.94            = (k2_mcart_1 @ sk_E_1))
% 0.69/0.94        | ((sk_B_1) = (k1_xboole_0))
% 0.69/0.94        | ((sk_A_1) = (k1_xboole_0)))),
% 0.69/0.94      inference('sup-', [status(thm)], ['132', '133'])).
% 0.69/0.94  thf('135', plain, (((sk_A_1) != (k1_xboole_0))),
% 0.69/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.94  thf('136', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.69/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.94  thf('137', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.69/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.94  thf('138', plain,
% 0.69/0.94      (((k7_mcart_1 @ sk_A_1 @ sk_B_1 @ sk_C_1 @ sk_E_1)
% 0.69/0.94         = (k2_mcart_1 @ sk_E_1))),
% 0.69/0.94      inference('simplify_reflect-', [status(thm)],
% 0.69/0.94                ['134', '135', '136', '137'])).
% 0.69/0.94  thf('139', plain, (((sk_D) != (k2_mcart_1 @ sk_E_1))),
% 0.69/0.94      inference('demod', [status(thm)], ['131', '138'])).
% 0.69/0.94  thf('140', plain, ($false),
% 0.69/0.94      inference('simplify_reflect-', [status(thm)], ['130', '139'])).
% 0.69/0.94  
% 0.69/0.94  % SZS output end Refutation
% 0.69/0.94  
% 0.77/0.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
