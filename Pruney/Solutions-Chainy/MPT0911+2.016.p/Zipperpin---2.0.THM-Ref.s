%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Wk0hbUqDbc

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:58 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :  182 ( 399 expanded)
%              Number of leaves         :   39 ( 139 expanded)
%              Depth                    :   27
%              Number of atoms          : 1603 (5619 expanded)
%              Number of equality atoms :  207 ( 748 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

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

thf('1',plain,(
    ! [X29: $i] :
      ( ( X29 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X29 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('2',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X24 ) @ X25 )
      | ~ ( r2_hidden @ X24 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ),
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
    ! [X29: $i] :
      ( ( X29 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X29 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

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

thf('10',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('12',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t23_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( A
          = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X27: $i,X28: $i] :
      ( ( X27
        = ( k4_tarski @ ( k1_mcart_1 @ X27 ) @ ( k2_mcart_1 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X28 )
      | ~ ( r2_hidden @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('14',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_zfmisc_1 @ X13 @ X14 @ X15 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('16',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( v1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('20',plain,
    ( ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('21',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k4_zfmisc_1 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X16 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t55_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 ) )
    <=> ( ( k4_zfmisc_1 @ A @ B @ C @ D )
       != k1_xboole_0 ) ) )).

thf('23',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( ( k4_zfmisc_1 @ X38 @ X39 @ X40 @ X41 )
       != k1_xboole_0 )
      | ( X41 = k1_xboole_0 )
      | ( X40 = k1_xboole_0 )
      | ( X39 = k1_xboole_0 )
      | ( X38 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['24','25','26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['9','28'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('30',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 )
      | ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X1: $i] :
      ( ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('34',plain,(
    ! [X1: $i] :
      ( ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('simplify_reflect+',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k1_xboole_0 != sk_E )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference(eq_fact,[status(thm)],['34'])).

thf('36',plain,(
    ! [X1: $i] :
      ( ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('simplify_reflect+',[status(thm)],['32','33'])).

thf('37',plain,
    ( sk_E
    = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('39',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_zfmisc_1 @ X13 @ X14 @ X15 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('40',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X24 ) @ X25 )
      | ~ ( r2_hidden @ X24 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X27: $i,X28: $i] :
      ( ( X27
        = ( k4_tarski @ ( k1_mcart_1 @ X27 ) @ ( k2_mcart_1 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X28 )
      | ~ ( r2_hidden @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('48',plain,
    ( ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('49',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_mcart_1 @ X10 @ X11 @ X12 )
      = ( k4_tarski @ ( k4_tarski @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X0 )
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('52',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X24 ) @ X26 )
      | ~ ( r2_hidden @ X24 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('53',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('55',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k4_zfmisc_1 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X16 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X38: $i,X39: $i,X40: $i,X42: $i] :
      ( ( X40 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X38 @ X39 @ X40 @ X42 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('59',plain,(
    ! [X38: $i,X39: $i,X42: $i] :
      ( ( k4_zfmisc_1 @ X38 @ X39 @ k1_xboole_0 @ X42 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_zfmisc_1 @ X13 @ X14 @ X15 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('61',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_zfmisc_1 @ X13 @ X14 @ X15 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k4_zfmisc_1 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X16 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k4_zfmisc_1 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X16 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 @ X4 )
      = ( k2_zfmisc_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) @ X4 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','66'])).

thf('68',plain,(
    ! [X38: $i,X39: $i,X40: $i,X42: $i] :
      ( ( X42 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X38 @ X39 @ X40 @ X42 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('69',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( k4_zfmisc_1 @ X38 @ X39 @ X40 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['67','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['57','70'])).

thf('72',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( ( k4_zfmisc_1 @ X38 @ X39 @ X40 @ X41 )
       != k1_xboole_0 )
      | ( X41 = k1_xboole_0 )
      | ( X40 = k1_xboole_0 )
      | ( X39 = k1_xboole_0 )
      | ( X38 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['74','75','76','77'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('79',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X3: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('84',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X43 @ sk_B_2 )
      | ( sk_E
       != ( k3_mcart_1 @ X44 @ X43 @ X45 ) )
      | ( sk_D = X45 )
      | ~ ( m1_subset_1 @ X45 @ sk_C )
      | ~ ( m1_subset_1 @ X44 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_D = X1 )
      | ( sk_E
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
        = k1_xboole_0 )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','86'])).

thf('88',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('89',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X24 ) @ X25 )
      | ~ ( r2_hidden @ X24 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('90',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('92',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k4_zfmisc_1 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X16 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['67','69'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( ( k4_zfmisc_1 @ X38 @ X39 @ X40 @ X41 )
       != k1_xboole_0 )
      | ( X41 = k1_xboole_0 )
      | ( X40 = k1_xboole_0 )
      | ( X39 = k1_xboole_0 )
      | ( X38 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['99','100','101','102'])).

thf('104',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X3: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('109',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
        = k1_xboole_0 )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['87','109'])).

thf('111',plain,
    ( ( sk_E != sk_E )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','110'])).

thf('112',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ) )).

thf('113',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( m1_subset_1 @ ( k7_mcart_1 @ X20 @ X21 @ X22 @ X23 ) @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k3_zfmisc_1 @ X20 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_mcart_1])).

thf('114',plain,(
    m1_subset_1 @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E ) @ sk_C ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
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

thf('116',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( X34 = k1_xboole_0 )
      | ( X35 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X34 @ X35 @ X37 @ X36 )
        = ( k2_mcart_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k3_zfmisc_1 @ X34 @ X35 @ X37 ) )
      | ( X37 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('117',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E )
      = ( k2_mcart_1 @ sk_E ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['117','118','119','120'])).

thf('122',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['114','121'])).

thf('123',plain,
    ( ( sk_E != sk_E )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['111','122'])).

thf('124',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    sk_D
 != ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['117','118','119','120'])).

thf('127',plain,(
    sk_D
 != ( k2_mcart_1 @ sk_E ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['124','127'])).

thf('129',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k4_zfmisc_1 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X16 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['67','69'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( ( k4_zfmisc_1 @ X38 @ X39 @ X40 @ X41 )
       != k1_xboole_0 )
      | ( X41 = k1_xboole_0 )
      | ( X40 = k1_xboole_0 )
      | ( X39 = k1_xboole_0 )
      | ( X38 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['135','136','137','138'])).

thf('140',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('141',plain,(
    $false ),
    inference(demod,[status(thm)],['0','139','140'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Wk0hbUqDbc
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:56:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.69/0.92  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.69/0.92  % Solved by: fo/fo7.sh
% 0.69/0.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.92  % done 684 iterations in 0.463s
% 0.69/0.92  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.69/0.92  % SZS output start Refutation
% 0.69/0.92  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.69/0.92  thf(sk_C_type, type, sk_C: $i).
% 0.69/0.92  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.69/0.92  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.92  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.69/0.92  thf(sk_E_type, type, sk_E: $i).
% 0.69/0.92  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.69/0.92  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.69/0.92  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.69/0.92  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.69/0.92  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.69/0.92  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.69/0.92  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.69/0.92  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.69/0.92  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.69/0.92  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.69/0.92  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.69/0.92  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.69/0.92  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.69/0.92  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.69/0.92  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.69/0.92  thf(sk_D_type, type, sk_D: $i).
% 0.69/0.92  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.69/0.92  thf(fc1_subset_1, axiom,
% 0.69/0.92    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.69/0.92  thf('0', plain, (![X3 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X3))),
% 0.69/0.92      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.69/0.92  thf(t34_mcart_1, axiom,
% 0.69/0.92    (![A:$i]:
% 0.69/0.92     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.69/0.92          ( ![B:$i]:
% 0.69/0.92            ( ~( ( r2_hidden @ B @ A ) & 
% 0.69/0.92                 ( ![C:$i,D:$i,E:$i,F:$i]:
% 0.69/0.92                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.69/0.92                        ( ( B ) = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) ) ) ) ) ))).
% 0.69/0.92  thf('1', plain,
% 0.69/0.92      (![X29 : $i]:
% 0.69/0.92         (((X29) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X29) @ X29))),
% 0.69/0.92      inference('cnf', [status(esa)], [t34_mcart_1])).
% 0.69/0.92  thf(t10_mcart_1, axiom,
% 0.69/0.92    (![A:$i,B:$i,C:$i]:
% 0.69/0.92     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.69/0.92       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.69/0.92         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.69/0.92  thf('2', plain,
% 0.69/0.92      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.69/0.92         ((r2_hidden @ (k1_mcart_1 @ X24) @ X25)
% 0.69/0.92          | ~ (r2_hidden @ X24 @ (k2_zfmisc_1 @ X25 @ X26)))),
% 0.69/0.92      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.69/0.92  thf('3', plain,
% 0.69/0.92      (![X0 : $i, X1 : $i]:
% 0.69/0.92         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 0.69/0.92          | (r2_hidden @ (k1_mcart_1 @ (sk_B_1 @ (k2_zfmisc_1 @ X1 @ X0))) @ X1))),
% 0.69/0.92      inference('sup-', [status(thm)], ['1', '2'])).
% 0.69/0.92  thf(d1_xboole_0, axiom,
% 0.69/0.92    (![A:$i]:
% 0.69/0.92     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.69/0.92  thf('4', plain,
% 0.69/0.92      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.69/0.92      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.69/0.92  thf('5', plain,
% 0.69/0.92      (![X0 : $i, X1 : $i]:
% 0.69/0.92         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.69/0.92      inference('sup-', [status(thm)], ['3', '4'])).
% 0.69/0.92  thf('6', plain,
% 0.69/0.92      (![X29 : $i]:
% 0.69/0.92         (((X29) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X29) @ X29))),
% 0.69/0.92      inference('cnf', [status(esa)], [t34_mcart_1])).
% 0.69/0.92  thf('7', plain,
% 0.69/0.92      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.69/0.92      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.69/0.92  thf('8', plain,
% 0.69/0.92      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.69/0.92      inference('sup-', [status(thm)], ['6', '7'])).
% 0.69/0.92  thf('9', plain,
% 0.69/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.92         (((X2) = (k2_zfmisc_1 @ X1 @ X0))
% 0.69/0.92          | ~ (v1_xboole_0 @ X1)
% 0.69/0.92          | ~ (v1_xboole_0 @ X2))),
% 0.69/0.92      inference('sup+', [status(thm)], ['5', '8'])).
% 0.69/0.92  thf(t71_mcart_1, conjecture,
% 0.69/0.92    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.69/0.92     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.69/0.92       ( ( ![F:$i]:
% 0.69/0.92           ( ( m1_subset_1 @ F @ A ) =>
% 0.69/0.92             ( ![G:$i]:
% 0.69/0.92               ( ( m1_subset_1 @ G @ B ) =>
% 0.69/0.92                 ( ![H:$i]:
% 0.69/0.92                   ( ( m1_subset_1 @ H @ C ) =>
% 0.69/0.92                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.69/0.92                       ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 0.69/0.92         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.69/0.92           ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.69/0.92           ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 0.69/0.92  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.92    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.69/0.92        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.69/0.92          ( ( ![F:$i]:
% 0.69/0.92              ( ( m1_subset_1 @ F @ A ) =>
% 0.69/0.92                ( ![G:$i]:
% 0.69/0.92                  ( ( m1_subset_1 @ G @ B ) =>
% 0.69/0.92                    ( ![H:$i]:
% 0.69/0.92                      ( ( m1_subset_1 @ H @ C ) =>
% 0.69/0.92                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.69/0.92                          ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 0.69/0.92            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.69/0.92              ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.69/0.92              ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 0.69/0.92    inference('cnf.neg', [status(esa)], [t71_mcart_1])).
% 0.69/0.92  thf('10', plain,
% 0.69/0.92      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf(t2_subset, axiom,
% 0.69/0.92    (![A:$i,B:$i]:
% 0.69/0.92     ( ( m1_subset_1 @ A @ B ) =>
% 0.69/0.92       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.69/0.92  thf('11', plain,
% 0.69/0.92      (![X6 : $i, X7 : $i]:
% 0.69/0.92         ((r2_hidden @ X6 @ X7)
% 0.69/0.92          | (v1_xboole_0 @ X7)
% 0.69/0.92          | ~ (m1_subset_1 @ X6 @ X7))),
% 0.69/0.92      inference('cnf', [status(esa)], [t2_subset])).
% 0.69/0.92  thf('12', plain,
% 0.69/0.92      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.69/0.92        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.69/0.92      inference('sup-', [status(thm)], ['10', '11'])).
% 0.69/0.92  thf(t23_mcart_1, axiom,
% 0.69/0.92    (![A:$i,B:$i]:
% 0.69/0.92     ( ( v1_relat_1 @ B ) =>
% 0.69/0.92       ( ( r2_hidden @ A @ B ) =>
% 0.69/0.92         ( ( A ) = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ))).
% 0.69/0.92  thf('13', plain,
% 0.69/0.92      (![X27 : $i, X28 : $i]:
% 0.69/0.92         (((X27) = (k4_tarski @ (k1_mcart_1 @ X27) @ (k2_mcart_1 @ X27)))
% 0.69/0.92          | ~ (v1_relat_1 @ X28)
% 0.69/0.92          | ~ (r2_hidden @ X27 @ X28))),
% 0.69/0.92      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.69/0.92  thf('14', plain,
% 0.69/0.92      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.69/0.92        | ~ (v1_relat_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.69/0.92        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.69/0.92      inference('sup-', [status(thm)], ['12', '13'])).
% 0.69/0.92  thf(d3_zfmisc_1, axiom,
% 0.69/0.92    (![A:$i,B:$i,C:$i]:
% 0.69/0.92     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.69/0.92       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.69/0.92  thf('15', plain,
% 0.69/0.92      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.69/0.92         ((k3_zfmisc_1 @ X13 @ X14 @ X15)
% 0.69/0.92           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14) @ X15))),
% 0.69/0.92      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.69/0.92  thf(fc6_relat_1, axiom,
% 0.69/0.92    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.69/0.92  thf('16', plain,
% 0.69/0.92      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.69/0.92      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.69/0.92  thf('17', plain,
% 0.69/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.92         (v1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))),
% 0.69/0.92      inference('sup+', [status(thm)], ['15', '16'])).
% 0.69/0.92  thf('18', plain,
% 0.69/0.92      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.69/0.92        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.69/0.92      inference('demod', [status(thm)], ['14', '17'])).
% 0.69/0.92  thf('19', plain,
% 0.69/0.92      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.69/0.92      inference('sup-', [status(thm)], ['6', '7'])).
% 0.69/0.92  thf('20', plain,
% 0.69/0.92      ((((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.69/0.92        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 0.69/0.92      inference('sup-', [status(thm)], ['18', '19'])).
% 0.69/0.92  thf(d4_zfmisc_1, axiom,
% 0.69/0.92    (![A:$i,B:$i,C:$i,D:$i]:
% 0.69/0.92     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.69/0.92       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.69/0.92  thf('21', plain,
% 0.69/0.92      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.69/0.92         ((k4_zfmisc_1 @ X16 @ X17 @ X18 @ X19)
% 0.69/0.92           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X16 @ X17 @ X18) @ X19))),
% 0.69/0.92      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.69/0.92  thf('22', plain,
% 0.69/0.92      (![X0 : $i]:
% 0.69/0.92         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0)
% 0.69/0.92            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.69/0.92          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.69/0.92      inference('sup+', [status(thm)], ['20', '21'])).
% 0.69/0.92  thf(t55_mcart_1, axiom,
% 0.69/0.92    (![A:$i,B:$i,C:$i,D:$i]:
% 0.69/0.92     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.69/0.92         ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) ) <=>
% 0.69/0.92       ( ( k4_zfmisc_1 @ A @ B @ C @ D ) != ( k1_xboole_0 ) ) ))).
% 0.69/0.92  thf('23', plain,
% 0.69/0.92      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.69/0.92         (((k4_zfmisc_1 @ X38 @ X39 @ X40 @ X41) != (k1_xboole_0))
% 0.69/0.92          | ((X41) = (k1_xboole_0))
% 0.69/0.92          | ((X40) = (k1_xboole_0))
% 0.69/0.92          | ((X39) = (k1_xboole_0))
% 0.69/0.92          | ((X38) = (k1_xboole_0)))),
% 0.69/0.92      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.69/0.92  thf('24', plain,
% 0.69/0.92      (![X0 : $i]:
% 0.69/0.92         (((k2_zfmisc_1 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 0.69/0.92          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.69/0.92          | ((sk_A) = (k1_xboole_0))
% 0.69/0.92          | ((sk_B_2) = (k1_xboole_0))
% 0.69/0.92          | ((sk_C) = (k1_xboole_0))
% 0.69/0.92          | ((X0) = (k1_xboole_0)))),
% 0.69/0.92      inference('sup-', [status(thm)], ['22', '23'])).
% 0.69/0.92  thf('25', plain, (((sk_C) != (k1_xboole_0))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf('26', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf('27', plain, (((sk_A) != (k1_xboole_0))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf('28', plain,
% 0.69/0.92      (![X0 : $i]:
% 0.69/0.92         (((k2_zfmisc_1 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 0.69/0.92          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.69/0.92          | ((X0) = (k1_xboole_0)))),
% 0.69/0.92      inference('simplify_reflect-', [status(thm)], ['24', '25', '26', '27'])).
% 0.69/0.92  thf('29', plain,
% 0.69/0.92      (![X0 : $i, X1 : $i]:
% 0.69/0.92         (((X0) != (k1_xboole_0))
% 0.69/0.92          | ~ (v1_xboole_0 @ X0)
% 0.69/0.92          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.69/0.92          | ((X1) = (k1_xboole_0))
% 0.69/0.92          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.69/0.92      inference('sup-', [status(thm)], ['9', '28'])).
% 0.69/0.92  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.69/0.92  thf('30', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.69/0.92      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.69/0.92  thf('31', plain,
% 0.69/0.92      (![X0 : $i, X1 : $i]:
% 0.69/0.92         (((X0) != (k1_xboole_0))
% 0.69/0.92          | ~ (v1_xboole_0 @ X0)
% 0.69/0.92          | ((X1) = (k1_xboole_0))
% 0.69/0.92          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.69/0.92      inference('demod', [status(thm)], ['29', '30'])).
% 0.69/0.92  thf('32', plain,
% 0.69/0.92      (![X1 : $i]:
% 0.69/0.92         (((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.69/0.92          | ((X1) = (k1_xboole_0))
% 0.69/0.92          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.69/0.92      inference('simplify', [status(thm)], ['31'])).
% 0.69/0.92  thf('33', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.69/0.92      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.69/0.92  thf('34', plain,
% 0.69/0.92      (![X1 : $i]:
% 0.69/0.92         (((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.69/0.92          | ((X1) = (k1_xboole_0)))),
% 0.69/0.92      inference('simplify_reflect+', [status(thm)], ['32', '33'])).
% 0.69/0.92  thf('35', plain,
% 0.69/0.92      ((((k1_xboole_0) != (sk_E))
% 0.69/0.92        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.69/0.92      inference('eq_fact', [status(thm)], ['34'])).
% 0.69/0.92  thf('36', plain,
% 0.69/0.92      (![X1 : $i]:
% 0.69/0.92         (((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.69/0.92          | ((X1) = (k1_xboole_0)))),
% 0.69/0.92      inference('simplify_reflect+', [status(thm)], ['32', '33'])).
% 0.69/0.92  thf('37', plain,
% 0.69/0.92      (((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))),
% 0.69/0.92      inference('clc', [status(thm)], ['35', '36'])).
% 0.69/0.92  thf('38', plain,
% 0.69/0.92      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.69/0.92        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 0.69/0.92      inference('sup-', [status(thm)], ['10', '11'])).
% 0.69/0.92  thf('39', plain,
% 0.69/0.92      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.69/0.92         ((k3_zfmisc_1 @ X13 @ X14 @ X15)
% 0.69/0.92           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14) @ X15))),
% 0.69/0.92      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.69/0.92  thf('40', plain,
% 0.69/0.92      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.69/0.92         ((r2_hidden @ (k1_mcart_1 @ X24) @ X25)
% 0.69/0.92          | ~ (r2_hidden @ X24 @ (k2_zfmisc_1 @ X25 @ X26)))),
% 0.69/0.92      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.69/0.92  thf('41', plain,
% 0.69/0.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.69/0.92         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.69/0.92          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.69/0.92      inference('sup-', [status(thm)], ['39', '40'])).
% 0.69/0.92  thf('42', plain,
% 0.69/0.92      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.69/0.92        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.69/0.92      inference('sup-', [status(thm)], ['38', '41'])).
% 0.69/0.92  thf('43', plain,
% 0.69/0.92      (![X27 : $i, X28 : $i]:
% 0.69/0.92         (((X27) = (k4_tarski @ (k1_mcart_1 @ X27) @ (k2_mcart_1 @ X27)))
% 0.69/0.92          | ~ (v1_relat_1 @ X28)
% 0.69/0.92          | ~ (r2_hidden @ X27 @ X28))),
% 0.69/0.92      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.69/0.92  thf('44', plain,
% 0.69/0.92      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.69/0.92        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))
% 0.69/0.92        | ((k1_mcart_1 @ sk_E)
% 0.69/0.92            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.69/0.92               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 0.69/0.92      inference('sup-', [status(thm)], ['42', '43'])).
% 0.69/0.92  thf('45', plain,
% 0.69/0.92      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.69/0.92      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.69/0.92  thf('46', plain,
% 0.69/0.92      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.69/0.92        | ((k1_mcart_1 @ sk_E)
% 0.69/0.92            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.69/0.92               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 0.69/0.92      inference('demod', [status(thm)], ['44', '45'])).
% 0.69/0.92  thf('47', plain,
% 0.69/0.92      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.69/0.92      inference('sup-', [status(thm)], ['6', '7'])).
% 0.69/0.92  thf('48', plain,
% 0.69/0.92      ((((k1_mcart_1 @ sk_E)
% 0.69/0.92          = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.69/0.92             (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 0.69/0.92        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 0.69/0.92      inference('sup-', [status(thm)], ['46', '47'])).
% 0.69/0.92  thf(d3_mcart_1, axiom,
% 0.69/0.92    (![A:$i,B:$i,C:$i]:
% 0.69/0.92     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.69/0.92  thf('49', plain,
% 0.69/0.92      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.69/0.92         ((k3_mcart_1 @ X10 @ X11 @ X12)
% 0.69/0.92           = (k4_tarski @ (k4_tarski @ X10 @ X11) @ X12))),
% 0.69/0.92      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.69/0.92  thf('50', plain,
% 0.69/0.92      (![X0 : $i]:
% 0.69/0.92         (((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.69/0.92            (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X0)
% 0.69/0.92            = (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.69/0.92          | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 0.69/0.92      inference('sup+', [status(thm)], ['48', '49'])).
% 0.69/0.92  thf('51', plain,
% 0.69/0.92      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.69/0.92        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.69/0.92      inference('sup-', [status(thm)], ['38', '41'])).
% 0.69/0.92  thf('52', plain,
% 0.69/0.92      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.69/0.92         ((r2_hidden @ (k2_mcart_1 @ X24) @ X26)
% 0.69/0.92          | ~ (r2_hidden @ X24 @ (k2_zfmisc_1 @ X25 @ X26)))),
% 0.69/0.92      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.69/0.92  thf('53', plain,
% 0.69/0.92      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.69/0.92        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2))),
% 0.69/0.92      inference('sup-', [status(thm)], ['51', '52'])).
% 0.69/0.92  thf('54', plain,
% 0.69/0.92      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.69/0.92      inference('sup-', [status(thm)], ['6', '7'])).
% 0.69/0.92  thf('55', plain,
% 0.69/0.92      (((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2)
% 0.69/0.92        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 0.69/0.92      inference('sup-', [status(thm)], ['53', '54'])).
% 0.69/0.92  thf('56', plain,
% 0.69/0.92      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.69/0.92         ((k4_zfmisc_1 @ X16 @ X17 @ X18 @ X19)
% 0.69/0.92           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X16 @ X17 @ X18) @ X19))),
% 0.69/0.92      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.69/0.92  thf('57', plain,
% 0.69/0.92      (![X0 : $i]:
% 0.69/0.92         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0)
% 0.69/0.92            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.69/0.92          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2))),
% 0.69/0.92      inference('sup+', [status(thm)], ['55', '56'])).
% 0.69/0.92  thf('58', plain,
% 0.69/0.92      (![X38 : $i, X39 : $i, X40 : $i, X42 : $i]:
% 0.69/0.92         (((X40) != (k1_xboole_0))
% 0.69/0.92          | ((k4_zfmisc_1 @ X38 @ X39 @ X40 @ X42) = (k1_xboole_0)))),
% 0.69/0.92      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.69/0.92  thf('59', plain,
% 0.69/0.92      (![X38 : $i, X39 : $i, X42 : $i]:
% 0.69/0.92         ((k4_zfmisc_1 @ X38 @ X39 @ k1_xboole_0 @ X42) = (k1_xboole_0))),
% 0.69/0.92      inference('simplify', [status(thm)], ['58'])).
% 0.69/0.92  thf('60', plain,
% 0.69/0.92      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.69/0.92         ((k3_zfmisc_1 @ X13 @ X14 @ X15)
% 0.69/0.92           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14) @ X15))),
% 0.69/0.92      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.69/0.92  thf('61', plain,
% 0.69/0.92      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.69/0.92         ((k3_zfmisc_1 @ X13 @ X14 @ X15)
% 0.69/0.92           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14) @ X15))),
% 0.69/0.92      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.69/0.92  thf('62', plain,
% 0.69/0.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.69/0.92         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.69/0.92           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 0.69/0.92      inference('sup+', [status(thm)], ['60', '61'])).
% 0.69/0.92  thf('63', plain,
% 0.69/0.92      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.69/0.92         ((k4_zfmisc_1 @ X16 @ X17 @ X18 @ X19)
% 0.69/0.92           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X16 @ X17 @ X18) @ X19))),
% 0.69/0.92      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.69/0.92  thf('64', plain,
% 0.69/0.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.69/0.92         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.69/0.92           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.69/0.92      inference('demod', [status(thm)], ['62', '63'])).
% 0.69/0.92  thf('65', plain,
% 0.69/0.92      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.69/0.92         ((k4_zfmisc_1 @ X16 @ X17 @ X18 @ X19)
% 0.69/0.92           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X16 @ X17 @ X18) @ X19))),
% 0.69/0.92      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.69/0.92  thf('66', plain,
% 0.69/0.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.69/0.92         ((k4_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0 @ X4)
% 0.69/0.92           = (k2_zfmisc_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) @ X4))),
% 0.69/0.92      inference('sup+', [status(thm)], ['64', '65'])).
% 0.69/0.92  thf('67', plain,
% 0.69/0.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.69/0.92         ((k1_xboole_0)
% 0.69/0.92           = (k2_zfmisc_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ k1_xboole_0) @ X0))),
% 0.69/0.92      inference('sup+', [status(thm)], ['59', '66'])).
% 0.69/0.92  thf('68', plain,
% 0.69/0.92      (![X38 : $i, X39 : $i, X40 : $i, X42 : $i]:
% 0.69/0.92         (((X42) != (k1_xboole_0))
% 0.69/0.92          | ((k4_zfmisc_1 @ X38 @ X39 @ X40 @ X42) = (k1_xboole_0)))),
% 0.69/0.92      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.69/0.92  thf('69', plain,
% 0.69/0.92      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.69/0.92         ((k4_zfmisc_1 @ X38 @ X39 @ X40 @ k1_xboole_0) = (k1_xboole_0))),
% 0.69/0.92      inference('simplify', [status(thm)], ['68'])).
% 0.69/0.92  thf('70', plain,
% 0.69/0.92      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.69/0.92      inference('demod', [status(thm)], ['67', '69'])).
% 0.69/0.92  thf('71', plain,
% 0.69/0.92      (![X0 : $i]:
% 0.69/0.92         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0) = (k1_xboole_0))
% 0.69/0.92          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2))),
% 0.69/0.92      inference('demod', [status(thm)], ['57', '70'])).
% 0.69/0.92  thf('72', plain,
% 0.69/0.92      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.69/0.92         (((k4_zfmisc_1 @ X38 @ X39 @ X40 @ X41) != (k1_xboole_0))
% 0.69/0.92          | ((X41) = (k1_xboole_0))
% 0.69/0.92          | ((X40) = (k1_xboole_0))
% 0.69/0.92          | ((X39) = (k1_xboole_0))
% 0.69/0.92          | ((X38) = (k1_xboole_0)))),
% 0.69/0.92      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.69/0.92  thf('73', plain,
% 0.69/0.92      (![X0 : $i]:
% 0.69/0.92         (((k1_xboole_0) != (k1_xboole_0))
% 0.69/0.92          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2)
% 0.69/0.92          | ((sk_A) = (k1_xboole_0))
% 0.69/0.92          | ((sk_B_2) = (k1_xboole_0))
% 0.69/0.92          | ((sk_C) = (k1_xboole_0))
% 0.69/0.92          | ((X0) = (k1_xboole_0)))),
% 0.69/0.92      inference('sup-', [status(thm)], ['71', '72'])).
% 0.69/0.92  thf('74', plain,
% 0.69/0.92      (![X0 : $i]:
% 0.69/0.92         (((X0) = (k1_xboole_0))
% 0.69/0.92          | ((sk_C) = (k1_xboole_0))
% 0.69/0.92          | ((sk_B_2) = (k1_xboole_0))
% 0.69/0.92          | ((sk_A) = (k1_xboole_0))
% 0.69/0.92          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2))),
% 0.69/0.92      inference('simplify', [status(thm)], ['73'])).
% 0.69/0.92  thf('75', plain, (((sk_A) != (k1_xboole_0))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf('76', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf('77', plain, (((sk_C) != (k1_xboole_0))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf('78', plain,
% 0.69/0.92      (![X0 : $i]:
% 0.69/0.92         (((X0) = (k1_xboole_0))
% 0.69/0.92          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2))),
% 0.69/0.92      inference('simplify_reflect-', [status(thm)], ['74', '75', '76', '77'])).
% 0.69/0.92  thf(t1_subset, axiom,
% 0.69/0.92    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.69/0.92  thf('79', plain,
% 0.69/0.92      (![X4 : $i, X5 : $i]: ((m1_subset_1 @ X4 @ X5) | ~ (r2_hidden @ X4 @ X5))),
% 0.69/0.92      inference('cnf', [status(esa)], [t1_subset])).
% 0.69/0.92  thf('80', plain,
% 0.69/0.92      (![X0 : $i]:
% 0.69/0.92         (((X0) = (k1_xboole_0))
% 0.69/0.92          | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2))),
% 0.69/0.92      inference('sup-', [status(thm)], ['78', '79'])).
% 0.69/0.92  thf('81', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.69/0.92      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.69/0.92  thf('82', plain,
% 0.69/0.92      (![X0 : $i]:
% 0.69/0.92         ((v1_xboole_0 @ X0)
% 0.69/0.92          | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2))),
% 0.69/0.92      inference('sup+', [status(thm)], ['80', '81'])).
% 0.69/0.92  thf('83', plain, (![X3 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X3))),
% 0.69/0.92      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.69/0.92  thf('84', plain,
% 0.69/0.92      ((m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2)),
% 0.69/0.92      inference('sup-', [status(thm)], ['82', '83'])).
% 0.69/0.92  thf('85', plain,
% 0.69/0.92      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.69/0.92         (~ (m1_subset_1 @ X43 @ sk_B_2)
% 0.69/0.92          | ((sk_E) != (k3_mcart_1 @ X44 @ X43 @ X45))
% 0.69/0.92          | ((sk_D) = (X45))
% 0.69/0.92          | ~ (m1_subset_1 @ X45 @ sk_C)
% 0.69/0.92          | ~ (m1_subset_1 @ X44 @ sk_A))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf('86', plain,
% 0.69/0.92      (![X0 : $i, X1 : $i]:
% 0.69/0.92         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.69/0.92          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.69/0.92          | ((sk_D) = (X1))
% 0.69/0.92          | ((sk_E)
% 0.69/0.92              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1)))),
% 0.69/0.92      inference('sup-', [status(thm)], ['84', '85'])).
% 0.69/0.92  thf('87', plain,
% 0.69/0.92      (![X0 : $i]:
% 0.69/0.92         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.69/0.92          | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0))
% 0.69/0.92          | ((sk_D) = (X0))
% 0.69/0.92          | ~ (m1_subset_1 @ X0 @ sk_C)
% 0.69/0.92          | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.69/0.92      inference('sup-', [status(thm)], ['50', '86'])).
% 0.69/0.92  thf('88', plain,
% 0.69/0.92      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.69/0.92        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.69/0.92      inference('sup-', [status(thm)], ['38', '41'])).
% 0.69/0.92  thf('89', plain,
% 0.69/0.92      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.69/0.92         ((r2_hidden @ (k1_mcart_1 @ X24) @ X25)
% 0.69/0.92          | ~ (r2_hidden @ X24 @ (k2_zfmisc_1 @ X25 @ X26)))),
% 0.69/0.92      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.69/0.92  thf('90', plain,
% 0.69/0.92      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 0.69/0.92        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.69/0.92      inference('sup-', [status(thm)], ['88', '89'])).
% 0.69/0.92  thf('91', plain,
% 0.69/0.92      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.69/0.92      inference('sup-', [status(thm)], ['6', '7'])).
% 0.69/0.92  thf('92', plain,
% 0.69/0.92      (((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 0.69/0.92        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 0.69/0.92      inference('sup-', [status(thm)], ['90', '91'])).
% 0.69/0.92  thf('93', plain,
% 0.69/0.92      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.69/0.92         ((k4_zfmisc_1 @ X16 @ X17 @ X18 @ X19)
% 0.69/0.92           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X16 @ X17 @ X18) @ X19))),
% 0.69/0.92      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.69/0.92  thf('94', plain,
% 0.69/0.92      (![X0 : $i]:
% 0.69/0.92         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0)
% 0.69/0.92            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.69/0.92          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.69/0.92      inference('sup+', [status(thm)], ['92', '93'])).
% 0.69/0.92  thf('95', plain,
% 0.69/0.92      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.69/0.92      inference('demod', [status(thm)], ['67', '69'])).
% 0.69/0.92  thf('96', plain,
% 0.69/0.92      (![X0 : $i]:
% 0.69/0.92         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0) = (k1_xboole_0))
% 0.69/0.92          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.69/0.92      inference('demod', [status(thm)], ['94', '95'])).
% 0.69/0.92  thf('97', plain,
% 0.69/0.92      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.69/0.92         (((k4_zfmisc_1 @ X38 @ X39 @ X40 @ X41) != (k1_xboole_0))
% 0.69/0.92          | ((X41) = (k1_xboole_0))
% 0.69/0.92          | ((X40) = (k1_xboole_0))
% 0.69/0.92          | ((X39) = (k1_xboole_0))
% 0.69/0.92          | ((X38) = (k1_xboole_0)))),
% 0.69/0.92      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.69/0.92  thf('98', plain,
% 0.69/0.92      (![X0 : $i]:
% 0.69/0.92         (((k1_xboole_0) != (k1_xboole_0))
% 0.69/0.92          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 0.69/0.92          | ((sk_A) = (k1_xboole_0))
% 0.69/0.92          | ((sk_B_2) = (k1_xboole_0))
% 0.69/0.92          | ((sk_C) = (k1_xboole_0))
% 0.69/0.92          | ((X0) = (k1_xboole_0)))),
% 0.69/0.92      inference('sup-', [status(thm)], ['96', '97'])).
% 0.69/0.92  thf('99', plain,
% 0.69/0.92      (![X0 : $i]:
% 0.69/0.92         (((X0) = (k1_xboole_0))
% 0.69/0.92          | ((sk_C) = (k1_xboole_0))
% 0.69/0.92          | ((sk_B_2) = (k1_xboole_0))
% 0.69/0.92          | ((sk_A) = (k1_xboole_0))
% 0.69/0.92          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.69/0.92      inference('simplify', [status(thm)], ['98'])).
% 0.69/0.92  thf('100', plain, (((sk_A) != (k1_xboole_0))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf('101', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf('102', plain, (((sk_C) != (k1_xboole_0))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf('103', plain,
% 0.69/0.92      (![X0 : $i]:
% 0.69/0.92         (((X0) = (k1_xboole_0))
% 0.69/0.92          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.69/0.92      inference('simplify_reflect-', [status(thm)], ['99', '100', '101', '102'])).
% 0.69/0.92  thf('104', plain,
% 0.69/0.92      (![X4 : $i, X5 : $i]: ((m1_subset_1 @ X4 @ X5) | ~ (r2_hidden @ X4 @ X5))),
% 0.69/0.92      inference('cnf', [status(esa)], [t1_subset])).
% 0.69/0.92  thf('105', plain,
% 0.69/0.92      (![X0 : $i]:
% 0.69/0.92         (((X0) = (k1_xboole_0))
% 0.69/0.92          | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.69/0.92      inference('sup-', [status(thm)], ['103', '104'])).
% 0.69/0.92  thf('106', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.69/0.92      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.69/0.92  thf('107', plain,
% 0.69/0.92      (![X0 : $i]:
% 0.69/0.92         ((v1_xboole_0 @ X0)
% 0.69/0.92          | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.69/0.92      inference('sup+', [status(thm)], ['105', '106'])).
% 0.69/0.92  thf('108', plain, (![X3 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X3))),
% 0.69/0.92      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.69/0.92  thf('109', plain,
% 0.69/0.92      ((m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)),
% 0.69/0.92      inference('sup-', [status(thm)], ['107', '108'])).
% 0.69/0.92  thf('110', plain,
% 0.69/0.92      (![X0 : $i]:
% 0.69/0.92         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.69/0.92          | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0))
% 0.69/0.92          | ((sk_D) = (X0))
% 0.69/0.92          | ~ (m1_subset_1 @ X0 @ sk_C))),
% 0.69/0.92      inference('demod', [status(thm)], ['87', '109'])).
% 0.69/0.92  thf('111', plain,
% 0.69/0.92      ((((sk_E) != (sk_E))
% 0.69/0.92        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)
% 0.69/0.92        | ((sk_D) = (k2_mcart_1 @ sk_E))
% 0.69/0.92        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 0.69/0.92      inference('sup-', [status(thm)], ['37', '110'])).
% 0.69/0.92  thf('112', plain,
% 0.69/0.92      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf(dt_k7_mcart_1, axiom,
% 0.69/0.92    (![A:$i,B:$i,C:$i,D:$i]:
% 0.69/0.92     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.69/0.92       ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ))).
% 0.69/0.92  thf('113', plain,
% 0.69/0.92      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.69/0.92         ((m1_subset_1 @ (k7_mcart_1 @ X20 @ X21 @ X22 @ X23) @ X22)
% 0.69/0.92          | ~ (m1_subset_1 @ X23 @ (k3_zfmisc_1 @ X20 @ X21 @ X22)))),
% 0.69/0.92      inference('cnf', [status(esa)], [dt_k7_mcart_1])).
% 0.69/0.92  thf('114', plain,
% 0.69/0.92      ((m1_subset_1 @ (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E) @ sk_C)),
% 0.69/0.92      inference('sup-', [status(thm)], ['112', '113'])).
% 0.69/0.92  thf('115', plain,
% 0.69/0.92      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf(t50_mcart_1, axiom,
% 0.69/0.92    (![A:$i,B:$i,C:$i]:
% 0.69/0.92     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.69/0.92          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.69/0.92          ( ~( ![D:$i]:
% 0.69/0.92               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.69/0.92                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.69/0.92                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.69/0.92                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.69/0.92                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.69/0.92                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.69/0.92  thf('116', plain,
% 0.69/0.92      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.69/0.92         (((X34) = (k1_xboole_0))
% 0.69/0.92          | ((X35) = (k1_xboole_0))
% 0.69/0.92          | ((k7_mcart_1 @ X34 @ X35 @ X37 @ X36) = (k2_mcart_1 @ X36))
% 0.69/0.92          | ~ (m1_subset_1 @ X36 @ (k3_zfmisc_1 @ X34 @ X35 @ X37))
% 0.69/0.92          | ((X37) = (k1_xboole_0)))),
% 0.69/0.92      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.69/0.92  thf('117', plain,
% 0.69/0.92      ((((sk_C) = (k1_xboole_0))
% 0.69/0.92        | ((k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))
% 0.69/0.92        | ((sk_B_2) = (k1_xboole_0))
% 0.69/0.92        | ((sk_A) = (k1_xboole_0)))),
% 0.69/0.92      inference('sup-', [status(thm)], ['115', '116'])).
% 0.69/0.92  thf('118', plain, (((sk_A) != (k1_xboole_0))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf('119', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf('120', plain, (((sk_C) != (k1_xboole_0))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf('121', plain,
% 0.69/0.92      (((k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))),
% 0.69/0.92      inference('simplify_reflect-', [status(thm)],
% 0.69/0.92                ['117', '118', '119', '120'])).
% 0.69/0.92  thf('122', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)),
% 0.69/0.92      inference('demod', [status(thm)], ['114', '121'])).
% 0.69/0.92  thf('123', plain,
% 0.69/0.92      ((((sk_E) != (sk_E))
% 0.69/0.92        | ((sk_D) = (k2_mcart_1 @ sk_E))
% 0.69/0.92        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 0.69/0.92      inference('demod', [status(thm)], ['111', '122'])).
% 0.69/0.92  thf('124', plain,
% 0.69/0.92      ((((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0))
% 0.69/0.92        | ((sk_D) = (k2_mcart_1 @ sk_E)))),
% 0.69/0.92      inference('simplify', [status(thm)], ['123'])).
% 0.69/0.92  thf('125', plain, (((sk_D) != (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf('126', plain,
% 0.69/0.92      (((k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))),
% 0.69/0.92      inference('simplify_reflect-', [status(thm)],
% 0.69/0.92                ['117', '118', '119', '120'])).
% 0.69/0.92  thf('127', plain, (((sk_D) != (k2_mcart_1 @ sk_E))),
% 0.69/0.92      inference('demod', [status(thm)], ['125', '126'])).
% 0.69/0.92  thf('128', plain, (((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0))),
% 0.69/0.92      inference('simplify_reflect-', [status(thm)], ['124', '127'])).
% 0.69/0.92  thf('129', plain,
% 0.69/0.92      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.69/0.92         ((k4_zfmisc_1 @ X16 @ X17 @ X18 @ X19)
% 0.69/0.92           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X16 @ X17 @ X18) @ X19))),
% 0.69/0.92      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.69/0.92  thf('130', plain,
% 0.69/0.92      (![X0 : $i]:
% 0.69/0.92         ((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0)
% 0.69/0.92           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.69/0.92      inference('sup+', [status(thm)], ['128', '129'])).
% 0.69/0.92  thf('131', plain,
% 0.69/0.92      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.69/0.92      inference('demod', [status(thm)], ['67', '69'])).
% 0.69/0.92  thf('132', plain,
% 0.69/0.92      (![X0 : $i]: ((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0) = (k1_xboole_0))),
% 0.69/0.92      inference('demod', [status(thm)], ['130', '131'])).
% 0.69/0.92  thf('133', plain,
% 0.69/0.92      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.69/0.92         (((k4_zfmisc_1 @ X38 @ X39 @ X40 @ X41) != (k1_xboole_0))
% 0.69/0.92          | ((X41) = (k1_xboole_0))
% 0.69/0.92          | ((X40) = (k1_xboole_0))
% 0.69/0.92          | ((X39) = (k1_xboole_0))
% 0.69/0.92          | ((X38) = (k1_xboole_0)))),
% 0.69/0.92      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.69/0.92  thf('134', plain,
% 0.69/0.92      (![X0 : $i]:
% 0.69/0.92         (((k1_xboole_0) != (k1_xboole_0))
% 0.69/0.92          | ((sk_A) = (k1_xboole_0))
% 0.69/0.92          | ((sk_B_2) = (k1_xboole_0))
% 0.69/0.92          | ((sk_C) = (k1_xboole_0))
% 0.69/0.92          | ((X0) = (k1_xboole_0)))),
% 0.69/0.92      inference('sup-', [status(thm)], ['132', '133'])).
% 0.69/0.92  thf('135', plain,
% 0.69/0.92      (![X0 : $i]:
% 0.69/0.92         (((X0) = (k1_xboole_0))
% 0.69/0.92          | ((sk_C) = (k1_xboole_0))
% 0.69/0.92          | ((sk_B_2) = (k1_xboole_0))
% 0.69/0.92          | ((sk_A) = (k1_xboole_0)))),
% 0.69/0.92      inference('simplify', [status(thm)], ['134'])).
% 0.69/0.92  thf('136', plain, (((sk_A) != (k1_xboole_0))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf('137', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf('138', plain, (((sk_C) != (k1_xboole_0))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf('139', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 0.69/0.92      inference('simplify_reflect-', [status(thm)],
% 0.69/0.92                ['135', '136', '137', '138'])).
% 0.69/0.92  thf('140', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.69/0.92      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.69/0.92  thf('141', plain, ($false),
% 0.69/0.92      inference('demod', [status(thm)], ['0', '139', '140'])).
% 0.69/0.92  
% 0.69/0.92  % SZS output end Refutation
% 0.69/0.92  
% 0.69/0.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
