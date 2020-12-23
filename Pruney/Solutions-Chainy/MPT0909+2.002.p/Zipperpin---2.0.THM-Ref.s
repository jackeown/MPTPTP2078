%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.j54SYBuw6R

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:50 EST 2020

% Result     : Theorem 11.46s
% Output     : Refutation 11.46s
% Verified   : 
% Statistics : Number of formulae       :  204 ( 719 expanded)
%              Number of leaves         :   40 ( 235 expanded)
%              Depth                    :   25
%              Number of atoms          : 1917 (10516 expanded)
%              Number of equality atoms :  242 (1335 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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

thf('0',plain,(
    ! [X43: $i] :
      ( ( X43 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X43 ) @ X43 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('1',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X38 ) @ X39 )
      | ~ ( r2_hidden @ X38 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( sk_B_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X43: $i] :
      ( ( X43 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X43 ) @ X43 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(t69_mcart_1,conjecture,(
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
                     => ( D = F ) ) ) ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( C = k1_xboole_0 )
          | ( D
            = ( k5_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )).

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
                       => ( D = F ) ) ) ) )
         => ( ( A = k1_xboole_0 )
            | ( B = k1_xboole_0 )
            | ( C = k1_xboole_0 )
            | ( D
              = ( k5_mcart_1 @ A @ B @ C @ E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t69_mcart_1])).

thf('9',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r2_hidden @ X18 @ X19 )
      | ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('11',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t23_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( A
          = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ) )).

thf('12',plain,(
    ! [X41: $i,X42: $i] :
      ( ( X41
        = ( k4_tarski @ ( k1_mcart_1 @ X41 ) @ ( k2_mcart_1 @ X41 ) ) )
      | ~ ( v1_relat_1 @ X42 )
      | ~ ( r2_hidden @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('13',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( sk_E_1
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_mcart_1 @ sk_E_1 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('14',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k3_zfmisc_1 @ X27 @ X28 @ X29 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('15',plain,(
    ! [X20: $i,X21: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( v1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( sk_E_1
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_mcart_1 @ sk_E_1 ) ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('19',plain,
    ( ( sk_E_1
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_mcart_1 @ sk_E_1 ) ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('20',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k4_zfmisc_1 @ X30 @ X31 @ X32 @ X33 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X30 @ X31 @ X32 ) @ X33 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_E_1
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_mcart_1 @ sk_E_1 ) ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t55_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 ) )
    <=> ( ( k4_zfmisc_1 @ A @ B @ C @ D )
       != k1_xboole_0 ) ) )).

thf('22',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( ( k4_zfmisc_1 @ X52 @ X53 @ X54 @ X55 )
       != k1_xboole_0 )
      | ( X55 = k1_xboole_0 )
      | ( X54 = k1_xboole_0 )
      | ( X53 = k1_xboole_0 )
      | ( X52 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ( sk_E_1
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_mcart_1 @ sk_E_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ( sk_E_1
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_mcart_1 @ sk_E_1 ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['23','24','25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( sk_E_1
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_mcart_1 @ sk_E_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','27'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('29',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('30',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('31',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( r1_tarski @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 )
      | ( sk_E_1
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_mcart_1 @ sk_E_1 ) ) ) ) ),
    inference(demod,[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X1: $i] :
      ( ( sk_E_1
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_mcart_1 @ sk_E_1 ) ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','32'])).

thf('37',plain,(
    ! [X1: $i] :
      ( ( sk_E_1
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_mcart_1 @ sk_E_1 ) ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('simplify_reflect+',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k1_xboole_0 != sk_E_1 )
    | ( sk_E_1
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_mcart_1 @ sk_E_1 ) ) ) ),
    inference(eq_fact,[status(thm)],['37'])).

thf('39',plain,(
    ! [X1: $i] :
      ( ( sk_E_1
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_mcart_1 @ sk_E_1 ) ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('simplify_reflect+',[status(thm)],['35','36'])).

thf('40',plain,
    ( sk_E_1
    = ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_mcart_1 @ sk_E_1 ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('42',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k3_zfmisc_1 @ X27 @ X28 @ X29 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('43',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X38 ) @ X39 )
      | ~ ( r2_hidden @ X38 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X41: $i,X42: $i] :
      ( ( X41
        = ( k4_tarski @ ( k1_mcart_1 @ X41 ) @ ( k2_mcart_1 @ X41 ) ) )
      | ~ ( v1_relat_1 @ X42 )
      | ~ ( r2_hidden @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('47',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
    | ( ( k1_mcart_1 @ sk_E_1 )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X20: $i,X21: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('49',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( ( k1_mcart_1 @ sk_E_1 )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( ( k1_mcart_1 @ sk_E_1 )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_mcart_1 @ sk_E_1 )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('54',plain,(
    ! [X52: $i,X53: $i,X54: $i,X56: $i] :
      ( ( X54 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X52 @ X53 @ X54 @ X56 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('55',plain,(
    ! [X52: $i,X53: $i,X56: $i] :
      ( ( k4_zfmisc_1 @ X52 @ X53 @ k1_xboole_0 @ X56 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k3_zfmisc_1 @ X27 @ X28 @ X29 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('57',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k3_zfmisc_1 @ X27 @ X28 @ X29 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k4_zfmisc_1 @ X30 @ X31 @ X32 @ X33 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X30 @ X31 @ X32 ) @ X33 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k4_zfmisc_1 @ X30 @ X31 @ X32 @ X33 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X30 @ X31 @ X32 ) @ X33 ) ) ),
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
    ! [X52: $i,X53: $i,X54: $i,X56: $i] :
      ( ( X56 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X52 @ X53 @ X54 @ X56 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('65',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( k4_zfmisc_1 @ X52 @ X53 @ X54 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['63','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['53','66'])).

thf('68',plain,(
    ! [X0: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) @ X0 ) )
      | ~ ( v1_xboole_0 @ X2 )
      | ( ( k1_mcart_1 @ sk_E_1 )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ) )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['52','67'])).

thf('69',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k4_zfmisc_1 @ X30 @ X31 @ X32 @ X33 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X30 @ X31 @ X32 ) @ X33 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('70',plain,(
    ! [X0: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 ) )
      | ~ ( v1_xboole_0 @ X2 )
      | ( ( k1_mcart_1 @ sk_E_1 )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ) )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k1_mcart_1 @ sk_E_1 )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ) )
      | ~ ( v1_xboole_0 @ X2 )
      | ( k1_xboole_0
        = ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( ( k4_zfmisc_1 @ X52 @ X53 @ X54 @ X55 )
       != k1_xboole_0 )
      | ( X55 = k1_xboole_0 )
      | ( X54 = k1_xboole_0 )
      | ( X53 = k1_xboole_0 )
      | ( X52 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( k1_mcart_1 @ sk_E_1 )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( ( k1_mcart_1 @ sk_E_1 )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k1_mcart_1 @ sk_E_1 )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['74','75','76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( ( k1_mcart_1 @ sk_E_1 )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ) )
      | ( ( k1_mcart_1 @ sk_E_1 )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k1_mcart_1 @ sk_E_1 )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k1_mcart_1 @ sk_E_1 )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k1_mcart_1 @ sk_E_1 )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ) )
      | ( ( k1_mcart_1 @ sk_E_1 )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_mcart_1 @ sk_E_1 )
        = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ) )
      | ( X1 = X0 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,
    ( ( k1_mcart_1 @ sk_E_1 )
    = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ) ),
    inference(condensation,[status(thm)],['83'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('85',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k3_mcart_1 @ X24 @ X25 @ X26 )
      = ( k4_tarski @ ( k4_tarski @ X24 @ X25 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ X0 )
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('88',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X38 ) @ X40 )
      | ~ ( r2_hidden @ X38 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('89',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('91',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_2 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k4_zfmisc_1 @ X30 @ X31 @ X32 @ X33 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X30 @ X31 @ X32 ) @ X33 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['63','65'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( ( k4_zfmisc_1 @ X52 @ X53 @ X54 @ X55 )
       != k1_xboole_0 )
      | ( X55 = k1_xboole_0 )
      | ( X54 = k1_xboole_0 )
      | ( X53 = k1_xboole_0 )
      | ( X52 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_2 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['98','99','100','101'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('103',plain,(
    ! [X16: $i,X17: $i] :
      ( ( m1_subset_1 @ X16 @ X17 )
      | ~ ( r2_hidden @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_2 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_2 )
      | ( X1 = X0 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    sk_D
 != ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
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

thf('110',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( X48 = k1_xboole_0 )
      | ( X49 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X48 @ X49 @ X51 @ X50 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X50 ) ) )
      | ~ ( m1_subset_1 @ X50 @ ( k3_zfmisc_1 @ X48 @ X49 @ X51 ) )
      | ( X51 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('111',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_1 )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_1 )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['111','112','113','114'])).

thf('116',plain,(
    sk_D
 != ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['108','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( sk_D != X0 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['107','116'])).

thf('118',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_2 ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ~ ( m1_subset_1 @ X57 @ sk_B_2 )
      | ( sk_D = X58 )
      | ( sk_E_1
       != ( k3_mcart_1 @ X58 @ X57 @ X59 ) )
      | ~ ( m1_subset_1 @ X59 @ sk_C )
      | ~ ( m1_subset_1 @ X58 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_E_1
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ X1 ) )
      | ( sk_D = X0 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( sk_E_1
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ X0 ) )
      | ( sk_D
        = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','120'])).

thf('122',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('123',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X38 ) @ X39 )
      | ~ ( r2_hidden @ X38 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('124',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('126',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k4_zfmisc_1 @ X30 @ X31 @ X32 @ X33 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X30 @ X31 @ X32 ) @ X33 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['63','65'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( ( k4_zfmisc_1 @ X52 @ X53 @ X54 @ X55 )
       != k1_xboole_0 )
      | ( X55 = k1_xboole_0 )
      | ( X54 = k1_xboole_0 )
      | ( X53 = k1_xboole_0 )
      | ( X52 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['133','134','135','136'])).

thf('138',plain,(
    ! [X16: $i,X17: $i] :
      ( ( m1_subset_1 @ X16 @ X17 )
      | ~ ( r2_hidden @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A )
      | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A )
      | ( X1 = X0 ) ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,(
    sk_D
 != ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['108','115'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( sk_D != X0 )
      | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( sk_E_1
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ X0 ) )
      | ( sk_D
        = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['121','145'])).

thf('147',plain,(
    sk_D
 != ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['108','115'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( sk_E_1
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['146','147'])).

thf('149',plain,
    ( ( sk_E_1 != sk_E_1 )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['40','148'])).

thf('150',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ) )).

thf('151',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( m1_subset_1 @ ( k7_mcart_1 @ X34 @ X35 @ X36 @ X37 ) @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k3_zfmisc_1 @ X34 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_mcart_1])).

thf('152',plain,(
    m1_subset_1 @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_1 ) @ sk_C ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( X48 = k1_xboole_0 )
      | ( X49 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X48 @ X49 @ X51 @ X50 )
        = ( k2_mcart_1 @ X50 ) )
      | ~ ( m1_subset_1 @ X50 @ ( k3_zfmisc_1 @ X48 @ X49 @ X51 ) )
      | ( X51 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('155',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_1 )
      = ( k2_mcart_1 @ sk_E_1 ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_1 )
    = ( k2_mcart_1 @ sk_E_1 ) ),
    inference('simplify_reflect-',[status(thm)],['155','156','157','158'])).

thf('160',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C ),
    inference(demod,[status(thm)],['152','159'])).

thf('161',plain,(
    sk_E_1 != sk_E_1 ),
    inference(demod,[status(thm)],['149','160'])).

thf('162',plain,(
    $false ),
    inference(simplify,[status(thm)],['161'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.j54SYBuw6R
% 0.14/0.36  % Computer   : n024.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 18:00:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 11.46/11.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 11.46/11.67  % Solved by: fo/fo7.sh
% 11.46/11.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 11.46/11.67  % done 9880 iterations in 11.194s
% 11.46/11.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 11.46/11.67  % SZS output start Refutation
% 11.46/11.67  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 11.46/11.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 11.46/11.67  thf(sk_D_type, type, sk_D: $i).
% 11.46/11.67  thf(sk_C_type, type, sk_C: $i).
% 11.46/11.67  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 11.46/11.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 11.46/11.67  thf(sk_B_2_type, type, sk_B_2: $i).
% 11.46/11.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 11.46/11.67  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 11.46/11.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 11.46/11.67  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 11.46/11.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 11.46/11.67  thf(sk_B_type, type, sk_B: $i > $i).
% 11.46/11.67  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 11.46/11.67  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 11.46/11.67  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 11.46/11.67  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 11.46/11.67  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 11.46/11.67  thf(sk_A_type, type, sk_A: $i).
% 11.46/11.67  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 11.46/11.67  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 11.46/11.67  thf(sk_E_1_type, type, sk_E_1: $i).
% 11.46/11.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 11.46/11.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 11.46/11.67  thf(t34_mcart_1, axiom,
% 11.46/11.67    (![A:$i]:
% 11.46/11.67     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 11.46/11.67          ( ![B:$i]:
% 11.46/11.67            ( ~( ( r2_hidden @ B @ A ) & 
% 11.46/11.67                 ( ![C:$i,D:$i,E:$i,F:$i]:
% 11.46/11.67                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 11.46/11.67                        ( ( B ) = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) ) ) ) ) ))).
% 11.46/11.67  thf('0', plain,
% 11.46/11.67      (![X43 : $i]:
% 11.46/11.67         (((X43) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X43) @ X43))),
% 11.46/11.67      inference('cnf', [status(esa)], [t34_mcart_1])).
% 11.46/11.67  thf(t10_mcart_1, axiom,
% 11.46/11.67    (![A:$i,B:$i,C:$i]:
% 11.46/11.67     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 11.46/11.67       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 11.46/11.67         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 11.46/11.67  thf('1', plain,
% 11.46/11.67      (![X38 : $i, X39 : $i, X40 : $i]:
% 11.46/11.67         ((r2_hidden @ (k1_mcart_1 @ X38) @ X39)
% 11.46/11.67          | ~ (r2_hidden @ X38 @ (k2_zfmisc_1 @ X39 @ X40)))),
% 11.46/11.67      inference('cnf', [status(esa)], [t10_mcart_1])).
% 11.46/11.67  thf('2', plain,
% 11.46/11.67      (![X0 : $i, X1 : $i]:
% 11.46/11.67         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 11.46/11.67          | (r2_hidden @ (k1_mcart_1 @ (sk_B_1 @ (k2_zfmisc_1 @ X1 @ X0))) @ X1))),
% 11.46/11.67      inference('sup-', [status(thm)], ['0', '1'])).
% 11.46/11.67  thf(d1_xboole_0, axiom,
% 11.46/11.67    (![A:$i]:
% 11.46/11.67     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 11.46/11.67  thf('3', plain,
% 11.46/11.67      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 11.46/11.67      inference('cnf', [status(esa)], [d1_xboole_0])).
% 11.46/11.67  thf('4', plain,
% 11.46/11.67      (![X0 : $i, X1 : $i]:
% 11.46/11.67         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 11.46/11.67      inference('sup-', [status(thm)], ['2', '3'])).
% 11.46/11.67  thf('5', plain,
% 11.46/11.67      (![X43 : $i]:
% 11.46/11.67         (((X43) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X43) @ X43))),
% 11.46/11.67      inference('cnf', [status(esa)], [t34_mcart_1])).
% 11.46/11.67  thf('6', plain,
% 11.46/11.67      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 11.46/11.67      inference('cnf', [status(esa)], [d1_xboole_0])).
% 11.46/11.67  thf('7', plain,
% 11.46/11.67      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 11.46/11.67      inference('sup-', [status(thm)], ['5', '6'])).
% 11.46/11.67  thf('8', plain,
% 11.46/11.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.46/11.67         (((X2) = (k2_zfmisc_1 @ X1 @ X0))
% 11.46/11.67          | ~ (v1_xboole_0 @ X1)
% 11.46/11.67          | ~ (v1_xboole_0 @ X2))),
% 11.46/11.67      inference('sup+', [status(thm)], ['4', '7'])).
% 11.46/11.67  thf(t69_mcart_1, conjecture,
% 11.46/11.67    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 11.46/11.67     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 11.46/11.67       ( ( ![F:$i]:
% 11.46/11.67           ( ( m1_subset_1 @ F @ A ) =>
% 11.46/11.67             ( ![G:$i]:
% 11.46/11.67               ( ( m1_subset_1 @ G @ B ) =>
% 11.46/11.67                 ( ![H:$i]:
% 11.46/11.67                   ( ( m1_subset_1 @ H @ C ) =>
% 11.46/11.67                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 11.46/11.67                       ( ( D ) = ( F ) ) ) ) ) ) ) ) ) =>
% 11.46/11.67         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 11.46/11.67           ( ( C ) = ( k1_xboole_0 ) ) | 
% 11.46/11.67           ( ( D ) = ( k5_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 11.46/11.67  thf(zf_stmt_0, negated_conjecture,
% 11.46/11.67    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 11.46/11.67        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 11.46/11.67          ( ( ![F:$i]:
% 11.46/11.67              ( ( m1_subset_1 @ F @ A ) =>
% 11.46/11.67                ( ![G:$i]:
% 11.46/11.67                  ( ( m1_subset_1 @ G @ B ) =>
% 11.46/11.67                    ( ![H:$i]:
% 11.46/11.67                      ( ( m1_subset_1 @ H @ C ) =>
% 11.46/11.67                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 11.46/11.67                          ( ( D ) = ( F ) ) ) ) ) ) ) ) ) =>
% 11.46/11.67            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 11.46/11.67              ( ( C ) = ( k1_xboole_0 ) ) | 
% 11.46/11.67              ( ( D ) = ( k5_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 11.46/11.67    inference('cnf.neg', [status(esa)], [t69_mcart_1])).
% 11.46/11.67  thf('9', plain,
% 11.46/11.67      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 11.46/11.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.46/11.67  thf(t2_subset, axiom,
% 11.46/11.67    (![A:$i,B:$i]:
% 11.46/11.67     ( ( m1_subset_1 @ A @ B ) =>
% 11.46/11.67       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 11.46/11.67  thf('10', plain,
% 11.46/11.67      (![X18 : $i, X19 : $i]:
% 11.46/11.67         ((r2_hidden @ X18 @ X19)
% 11.46/11.67          | (v1_xboole_0 @ X19)
% 11.46/11.67          | ~ (m1_subset_1 @ X18 @ X19))),
% 11.46/11.67      inference('cnf', [status(esa)], [t2_subset])).
% 11.46/11.67  thf('11', plain,
% 11.46/11.67      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 11.46/11.67        | (r2_hidden @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 11.46/11.67      inference('sup-', [status(thm)], ['9', '10'])).
% 11.46/11.67  thf(t23_mcart_1, axiom,
% 11.46/11.67    (![A:$i,B:$i]:
% 11.46/11.67     ( ( v1_relat_1 @ B ) =>
% 11.46/11.67       ( ( r2_hidden @ A @ B ) =>
% 11.46/11.67         ( ( A ) = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ))).
% 11.46/11.67  thf('12', plain,
% 11.46/11.67      (![X41 : $i, X42 : $i]:
% 11.46/11.67         (((X41) = (k4_tarski @ (k1_mcart_1 @ X41) @ (k2_mcart_1 @ X41)))
% 11.46/11.67          | ~ (v1_relat_1 @ X42)
% 11.46/11.67          | ~ (r2_hidden @ X41 @ X42))),
% 11.46/11.67      inference('cnf', [status(esa)], [t23_mcart_1])).
% 11.46/11.67  thf('13', plain,
% 11.46/11.67      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 11.46/11.67        | ~ (v1_relat_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 11.46/11.67        | ((sk_E_1)
% 11.46/11.67            = (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (k2_mcart_1 @ sk_E_1))))),
% 11.46/11.67      inference('sup-', [status(thm)], ['11', '12'])).
% 11.46/11.67  thf(d3_zfmisc_1, axiom,
% 11.46/11.67    (![A:$i,B:$i,C:$i]:
% 11.46/11.67     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 11.46/11.67       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 11.46/11.67  thf('14', plain,
% 11.46/11.67      (![X27 : $i, X28 : $i, X29 : $i]:
% 11.46/11.67         ((k3_zfmisc_1 @ X27 @ X28 @ X29)
% 11.46/11.67           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28) @ X29))),
% 11.46/11.67      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 11.46/11.67  thf(fc6_relat_1, axiom,
% 11.46/11.67    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 11.46/11.67  thf('15', plain,
% 11.46/11.67      (![X20 : $i, X21 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X20 @ X21))),
% 11.46/11.67      inference('cnf', [status(esa)], [fc6_relat_1])).
% 11.46/11.67  thf('16', plain,
% 11.46/11.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.46/11.67         (v1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))),
% 11.46/11.67      inference('sup+', [status(thm)], ['14', '15'])).
% 11.46/11.67  thf('17', plain,
% 11.46/11.67      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 11.46/11.67        | ((sk_E_1)
% 11.46/11.67            = (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (k2_mcart_1 @ sk_E_1))))),
% 11.46/11.67      inference('demod', [status(thm)], ['13', '16'])).
% 11.46/11.67  thf('18', plain,
% 11.46/11.67      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 11.46/11.67      inference('sup-', [status(thm)], ['5', '6'])).
% 11.46/11.67  thf('19', plain,
% 11.46/11.67      ((((sk_E_1) = (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (k2_mcart_1 @ sk_E_1)))
% 11.46/11.67        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 11.46/11.67      inference('sup-', [status(thm)], ['17', '18'])).
% 11.46/11.67  thf(d4_zfmisc_1, axiom,
% 11.46/11.67    (![A:$i,B:$i,C:$i,D:$i]:
% 11.46/11.67     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 11.46/11.67       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 11.46/11.67  thf('20', plain,
% 11.46/11.67      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 11.46/11.67         ((k4_zfmisc_1 @ X30 @ X31 @ X32 @ X33)
% 11.46/11.67           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X30 @ X31 @ X32) @ X33))),
% 11.46/11.67      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 11.46/11.67  thf('21', plain,
% 11.46/11.67      (![X0 : $i]:
% 11.46/11.67         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0)
% 11.46/11.67            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 11.46/11.67          | ((sk_E_1)
% 11.46/11.67              = (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (k2_mcart_1 @ sk_E_1))))),
% 11.46/11.67      inference('sup+', [status(thm)], ['19', '20'])).
% 11.46/11.67  thf(t55_mcart_1, axiom,
% 11.46/11.67    (![A:$i,B:$i,C:$i,D:$i]:
% 11.46/11.67     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 11.46/11.67         ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) ) <=>
% 11.46/11.67       ( ( k4_zfmisc_1 @ A @ B @ C @ D ) != ( k1_xboole_0 ) ) ))).
% 11.46/11.67  thf('22', plain,
% 11.46/11.67      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 11.46/11.67         (((k4_zfmisc_1 @ X52 @ X53 @ X54 @ X55) != (k1_xboole_0))
% 11.46/11.67          | ((X55) = (k1_xboole_0))
% 11.46/11.67          | ((X54) = (k1_xboole_0))
% 11.46/11.67          | ((X53) = (k1_xboole_0))
% 11.46/11.67          | ((X52) = (k1_xboole_0)))),
% 11.46/11.67      inference('cnf', [status(esa)], [t55_mcart_1])).
% 11.46/11.67  thf('23', plain,
% 11.46/11.67      (![X0 : $i]:
% 11.46/11.67         (((k2_zfmisc_1 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 11.46/11.67          | ((sk_E_1)
% 11.46/11.67              = (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (k2_mcart_1 @ sk_E_1)))
% 11.46/11.67          | ((sk_A) = (k1_xboole_0))
% 11.46/11.67          | ((sk_B_2) = (k1_xboole_0))
% 11.46/11.67          | ((sk_C) = (k1_xboole_0))
% 11.46/11.67          | ((X0) = (k1_xboole_0)))),
% 11.46/11.67      inference('sup-', [status(thm)], ['21', '22'])).
% 11.46/11.67  thf('24', plain, (((sk_C) != (k1_xboole_0))),
% 11.46/11.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.46/11.67  thf('25', plain, (((sk_B_2) != (k1_xboole_0))),
% 11.46/11.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.46/11.67  thf('26', plain, (((sk_A) != (k1_xboole_0))),
% 11.46/11.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.46/11.67  thf('27', plain,
% 11.46/11.67      (![X0 : $i]:
% 11.46/11.67         (((k2_zfmisc_1 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 11.46/11.67          | ((sk_E_1)
% 11.46/11.67              = (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (k2_mcart_1 @ sk_E_1)))
% 11.46/11.67          | ((X0) = (k1_xboole_0)))),
% 11.46/11.67      inference('simplify_reflect-', [status(thm)], ['23', '24', '25', '26'])).
% 11.46/11.67  thf('28', plain,
% 11.46/11.67      (![X0 : $i, X1 : $i]:
% 11.46/11.67         (((X0) != (k1_xboole_0))
% 11.46/11.67          | ~ (v1_xboole_0 @ X0)
% 11.46/11.67          | ~ (v1_xboole_0 @ k1_xboole_0)
% 11.46/11.67          | ((X1) = (k1_xboole_0))
% 11.46/11.67          | ((sk_E_1)
% 11.46/11.67              = (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (k2_mcart_1 @ sk_E_1))))),
% 11.46/11.67      inference('sup-', [status(thm)], ['8', '27'])).
% 11.46/11.67  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 11.46/11.67  thf('29', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 11.46/11.67      inference('cnf', [status(esa)], [t2_xboole_1])).
% 11.46/11.67  thf('30', plain,
% 11.46/11.67      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 11.46/11.67      inference('cnf', [status(esa)], [d1_xboole_0])).
% 11.46/11.67  thf(t7_ordinal1, axiom,
% 11.46/11.67    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 11.46/11.67  thf('31', plain,
% 11.46/11.67      (![X22 : $i, X23 : $i]:
% 11.46/11.67         (~ (r2_hidden @ X22 @ X23) | ~ (r1_tarski @ X23 @ X22))),
% 11.46/11.67      inference('cnf', [status(esa)], [t7_ordinal1])).
% 11.46/11.67  thf('32', plain,
% 11.46/11.67      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 11.46/11.67      inference('sup-', [status(thm)], ['30', '31'])).
% 11.46/11.67  thf('33', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.46/11.67      inference('sup-', [status(thm)], ['29', '32'])).
% 11.46/11.67  thf('34', plain,
% 11.46/11.67      (![X0 : $i, X1 : $i]:
% 11.46/11.67         (((X0) != (k1_xboole_0))
% 11.46/11.67          | ~ (v1_xboole_0 @ X0)
% 11.46/11.67          | ((X1) = (k1_xboole_0))
% 11.46/11.67          | ((sk_E_1)
% 11.46/11.67              = (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (k2_mcart_1 @ sk_E_1))))),
% 11.46/11.67      inference('demod', [status(thm)], ['28', '33'])).
% 11.46/11.67  thf('35', plain,
% 11.46/11.67      (![X1 : $i]:
% 11.46/11.67         (((sk_E_1)
% 11.46/11.67            = (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (k2_mcart_1 @ sk_E_1)))
% 11.46/11.67          | ((X1) = (k1_xboole_0))
% 11.46/11.67          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 11.46/11.67      inference('simplify', [status(thm)], ['34'])).
% 11.46/11.67  thf('36', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.46/11.67      inference('sup-', [status(thm)], ['29', '32'])).
% 11.46/11.67  thf('37', plain,
% 11.46/11.67      (![X1 : $i]:
% 11.46/11.67         (((sk_E_1)
% 11.46/11.67            = (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (k2_mcart_1 @ sk_E_1)))
% 11.46/11.67          | ((X1) = (k1_xboole_0)))),
% 11.46/11.67      inference('simplify_reflect+', [status(thm)], ['35', '36'])).
% 11.46/11.67  thf('38', plain,
% 11.46/11.67      ((((k1_xboole_0) != (sk_E_1))
% 11.46/11.67        | ((sk_E_1)
% 11.46/11.67            = (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (k2_mcart_1 @ sk_E_1))))),
% 11.46/11.67      inference('eq_fact', [status(thm)], ['37'])).
% 11.46/11.67  thf('39', plain,
% 11.46/11.67      (![X1 : $i]:
% 11.46/11.67         (((sk_E_1)
% 11.46/11.67            = (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (k2_mcart_1 @ sk_E_1)))
% 11.46/11.67          | ((X1) = (k1_xboole_0)))),
% 11.46/11.67      inference('simplify_reflect+', [status(thm)], ['35', '36'])).
% 11.46/11.67  thf('40', plain,
% 11.46/11.67      (((sk_E_1) = (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (k2_mcart_1 @ sk_E_1)))),
% 11.46/11.67      inference('clc', [status(thm)], ['38', '39'])).
% 11.46/11.67  thf('41', plain,
% 11.46/11.67      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 11.46/11.67        | (r2_hidden @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 11.46/11.67      inference('sup-', [status(thm)], ['9', '10'])).
% 11.46/11.67  thf('42', plain,
% 11.46/11.67      (![X27 : $i, X28 : $i, X29 : $i]:
% 11.46/11.67         ((k3_zfmisc_1 @ X27 @ X28 @ X29)
% 11.46/11.67           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28) @ X29))),
% 11.46/11.67      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 11.46/11.67  thf('43', plain,
% 11.46/11.67      (![X38 : $i, X39 : $i, X40 : $i]:
% 11.46/11.67         ((r2_hidden @ (k1_mcart_1 @ X38) @ X39)
% 11.46/11.67          | ~ (r2_hidden @ X38 @ (k2_zfmisc_1 @ X39 @ X40)))),
% 11.46/11.67      inference('cnf', [status(esa)], [t10_mcart_1])).
% 11.46/11.67  thf('44', plain,
% 11.46/11.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.46/11.67         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 11.46/11.67          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 11.46/11.67      inference('sup-', [status(thm)], ['42', '43'])).
% 11.46/11.67  thf('45', plain,
% 11.46/11.67      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 11.46/11.67        | (r2_hidden @ (k1_mcart_1 @ sk_E_1) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 11.46/11.67      inference('sup-', [status(thm)], ['41', '44'])).
% 11.46/11.67  thf('46', plain,
% 11.46/11.67      (![X41 : $i, X42 : $i]:
% 11.46/11.67         (((X41) = (k4_tarski @ (k1_mcart_1 @ X41) @ (k2_mcart_1 @ X41)))
% 11.46/11.67          | ~ (v1_relat_1 @ X42)
% 11.46/11.67          | ~ (r2_hidden @ X41 @ X42))),
% 11.46/11.67      inference('cnf', [status(esa)], [t23_mcart_1])).
% 11.46/11.67  thf('47', plain,
% 11.46/11.67      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 11.46/11.67        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))
% 11.46/11.67        | ((k1_mcart_1 @ sk_E_1)
% 11.46/11.67            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 11.46/11.67               (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)))))),
% 11.46/11.67      inference('sup-', [status(thm)], ['45', '46'])).
% 11.46/11.67  thf('48', plain,
% 11.46/11.67      (![X20 : $i, X21 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X20 @ X21))),
% 11.46/11.67      inference('cnf', [status(esa)], [fc6_relat_1])).
% 11.46/11.67  thf('49', plain,
% 11.46/11.67      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 11.46/11.67        | ((k1_mcart_1 @ sk_E_1)
% 11.46/11.67            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 11.46/11.67               (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)))))),
% 11.46/11.67      inference('demod', [status(thm)], ['47', '48'])).
% 11.46/11.67  thf('50', plain,
% 11.46/11.67      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 11.46/11.67        | ((k1_mcart_1 @ sk_E_1)
% 11.46/11.67            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 11.46/11.67               (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)))))),
% 11.46/11.67      inference('demod', [status(thm)], ['47', '48'])).
% 11.46/11.67  thf('51', plain,
% 11.46/11.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.46/11.67         (((X2) = (k2_zfmisc_1 @ X1 @ X0))
% 11.46/11.67          | ~ (v1_xboole_0 @ X1)
% 11.46/11.67          | ~ (v1_xboole_0 @ X2))),
% 11.46/11.67      inference('sup+', [status(thm)], ['4', '7'])).
% 11.46/11.67  thf('52', plain,
% 11.46/11.67      (![X0 : $i, X1 : $i]:
% 11.46/11.67         (((k1_mcart_1 @ sk_E_1)
% 11.46/11.67            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 11.46/11.67               (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))))
% 11.46/11.67          | ~ (v1_xboole_0 @ X0)
% 11.46/11.67          | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k2_zfmisc_1 @ X0 @ X1)))),
% 11.46/11.67      inference('sup-', [status(thm)], ['50', '51'])).
% 11.46/11.67  thf('53', plain,
% 11.46/11.67      (![X0 : $i, X1 : $i]:
% 11.46/11.67         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 11.46/11.67      inference('sup-', [status(thm)], ['2', '3'])).
% 11.46/11.67  thf('54', plain,
% 11.46/11.67      (![X52 : $i, X53 : $i, X54 : $i, X56 : $i]:
% 11.46/11.67         (((X54) != (k1_xboole_0))
% 11.46/11.67          | ((k4_zfmisc_1 @ X52 @ X53 @ X54 @ X56) = (k1_xboole_0)))),
% 11.46/11.67      inference('cnf', [status(esa)], [t55_mcart_1])).
% 11.46/11.67  thf('55', plain,
% 11.46/11.67      (![X52 : $i, X53 : $i, X56 : $i]:
% 11.46/11.67         ((k4_zfmisc_1 @ X52 @ X53 @ k1_xboole_0 @ X56) = (k1_xboole_0))),
% 11.46/11.67      inference('simplify', [status(thm)], ['54'])).
% 11.46/11.67  thf('56', plain,
% 11.46/11.67      (![X27 : $i, X28 : $i, X29 : $i]:
% 11.46/11.67         ((k3_zfmisc_1 @ X27 @ X28 @ X29)
% 11.46/11.67           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28) @ X29))),
% 11.46/11.67      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 11.46/11.67  thf('57', plain,
% 11.46/11.67      (![X27 : $i, X28 : $i, X29 : $i]:
% 11.46/11.67         ((k3_zfmisc_1 @ X27 @ X28 @ X29)
% 11.46/11.67           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28) @ X29))),
% 11.46/11.67      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 11.46/11.67  thf('58', plain,
% 11.46/11.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.46/11.67         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 11.46/11.67           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 11.46/11.67      inference('sup+', [status(thm)], ['56', '57'])).
% 11.46/11.67  thf('59', plain,
% 11.46/11.67      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 11.46/11.67         ((k4_zfmisc_1 @ X30 @ X31 @ X32 @ X33)
% 11.46/11.67           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X30 @ X31 @ X32) @ X33))),
% 11.46/11.67      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 11.46/11.67  thf('60', plain,
% 11.46/11.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.46/11.67         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 11.46/11.67           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 11.46/11.67      inference('demod', [status(thm)], ['58', '59'])).
% 11.46/11.67  thf('61', plain,
% 11.46/11.67      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 11.46/11.67         ((k4_zfmisc_1 @ X30 @ X31 @ X32 @ X33)
% 11.46/11.67           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X30 @ X31 @ X32) @ X33))),
% 11.46/11.67      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 11.46/11.67  thf('62', plain,
% 11.46/11.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 11.46/11.67         ((k4_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0 @ X4)
% 11.46/11.67           = (k2_zfmisc_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) @ X4))),
% 11.46/11.67      inference('sup+', [status(thm)], ['60', '61'])).
% 11.46/11.67  thf('63', plain,
% 11.46/11.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.46/11.67         ((k1_xboole_0)
% 11.46/11.67           = (k2_zfmisc_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ k1_xboole_0) @ X0))),
% 11.46/11.67      inference('sup+', [status(thm)], ['55', '62'])).
% 11.46/11.67  thf('64', plain,
% 11.46/11.67      (![X52 : $i, X53 : $i, X54 : $i, X56 : $i]:
% 11.46/11.67         (((X56) != (k1_xboole_0))
% 11.46/11.67          | ((k4_zfmisc_1 @ X52 @ X53 @ X54 @ X56) = (k1_xboole_0)))),
% 11.46/11.67      inference('cnf', [status(esa)], [t55_mcart_1])).
% 11.46/11.67  thf('65', plain,
% 11.46/11.67      (![X52 : $i, X53 : $i, X54 : $i]:
% 11.46/11.67         ((k4_zfmisc_1 @ X52 @ X53 @ X54 @ k1_xboole_0) = (k1_xboole_0))),
% 11.46/11.67      inference('simplify', [status(thm)], ['64'])).
% 11.46/11.67  thf('66', plain,
% 11.46/11.67      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 11.46/11.67      inference('demod', [status(thm)], ['63', '65'])).
% 11.46/11.67  thf('67', plain,
% 11.46/11.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.46/11.67         (((k1_xboole_0) = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X2))
% 11.46/11.67          | ~ (v1_xboole_0 @ X1))),
% 11.46/11.67      inference('sup+', [status(thm)], ['53', '66'])).
% 11.46/11.67  thf('68', plain,
% 11.46/11.67      (![X0 : $i, X2 : $i]:
% 11.46/11.67         (((k1_xboole_0)
% 11.46/11.67            = (k2_zfmisc_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) @ X0))
% 11.46/11.67          | ~ (v1_xboole_0 @ X2)
% 11.46/11.67          | ((k1_mcart_1 @ sk_E_1)
% 11.46/11.67              = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 11.46/11.67                 (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))))
% 11.46/11.67          | ~ (v1_xboole_0 @ X2))),
% 11.46/11.67      inference('sup+', [status(thm)], ['52', '67'])).
% 11.46/11.67  thf('69', plain,
% 11.46/11.67      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 11.46/11.67         ((k4_zfmisc_1 @ X30 @ X31 @ X32 @ X33)
% 11.46/11.67           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X30 @ X31 @ X32) @ X33))),
% 11.46/11.67      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 11.46/11.67  thf('70', plain,
% 11.46/11.67      (![X0 : $i, X2 : $i]:
% 11.46/11.67         (((k1_xboole_0) = (k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0))
% 11.46/11.67          | ~ (v1_xboole_0 @ X2)
% 11.46/11.67          | ((k1_mcart_1 @ sk_E_1)
% 11.46/11.67              = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 11.46/11.67                 (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))))
% 11.46/11.67          | ~ (v1_xboole_0 @ X2))),
% 11.46/11.67      inference('demod', [status(thm)], ['68', '69'])).
% 11.46/11.67  thf('71', plain,
% 11.46/11.67      (![X0 : $i, X2 : $i]:
% 11.46/11.67         (((k1_mcart_1 @ sk_E_1)
% 11.46/11.67            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 11.46/11.67               (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))))
% 11.46/11.67          | ~ (v1_xboole_0 @ X2)
% 11.46/11.67          | ((k1_xboole_0) = (k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0)))),
% 11.46/11.67      inference('simplify', [status(thm)], ['70'])).
% 11.46/11.67  thf('72', plain,
% 11.46/11.67      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 11.46/11.67         (((k4_zfmisc_1 @ X52 @ X53 @ X54 @ X55) != (k1_xboole_0))
% 11.46/11.67          | ((X55) = (k1_xboole_0))
% 11.46/11.67          | ((X54) = (k1_xboole_0))
% 11.46/11.67          | ((X53) = (k1_xboole_0))
% 11.46/11.67          | ((X52) = (k1_xboole_0)))),
% 11.46/11.67      inference('cnf', [status(esa)], [t55_mcart_1])).
% 11.46/11.67  thf('73', plain,
% 11.46/11.67      (![X0 : $i, X1 : $i]:
% 11.46/11.67         (((k1_xboole_0) != (k1_xboole_0))
% 11.46/11.67          | ~ (v1_xboole_0 @ X1)
% 11.46/11.67          | ((k1_mcart_1 @ sk_E_1)
% 11.46/11.67              = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 11.46/11.67                 (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))))
% 11.46/11.67          | ((sk_A) = (k1_xboole_0))
% 11.46/11.67          | ((sk_B_2) = (k1_xboole_0))
% 11.46/11.67          | ((sk_C) = (k1_xboole_0))
% 11.46/11.67          | ((X0) = (k1_xboole_0)))),
% 11.46/11.67      inference('sup-', [status(thm)], ['71', '72'])).
% 11.46/11.67  thf('74', plain,
% 11.46/11.67      (![X0 : $i, X1 : $i]:
% 11.46/11.67         (((X0) = (k1_xboole_0))
% 11.46/11.67          | ((sk_C) = (k1_xboole_0))
% 11.46/11.67          | ((sk_B_2) = (k1_xboole_0))
% 11.46/11.67          | ((sk_A) = (k1_xboole_0))
% 11.46/11.67          | ((k1_mcart_1 @ sk_E_1)
% 11.46/11.67              = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 11.46/11.67                 (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))))
% 11.46/11.67          | ~ (v1_xboole_0 @ X1))),
% 11.46/11.67      inference('simplify', [status(thm)], ['73'])).
% 11.46/11.67  thf('75', plain, (((sk_A) != (k1_xboole_0))),
% 11.46/11.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.46/11.67  thf('76', plain, (((sk_B_2) != (k1_xboole_0))),
% 11.46/11.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.46/11.67  thf('77', plain, (((sk_C) != (k1_xboole_0))),
% 11.46/11.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.46/11.67  thf('78', plain,
% 11.46/11.67      (![X0 : $i, X1 : $i]:
% 11.46/11.67         (((X0) = (k1_xboole_0))
% 11.46/11.67          | ((k1_mcart_1 @ sk_E_1)
% 11.46/11.67              = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 11.46/11.67                 (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))))
% 11.46/11.67          | ~ (v1_xboole_0 @ X1))),
% 11.46/11.67      inference('simplify_reflect-', [status(thm)], ['74', '75', '76', '77'])).
% 11.46/11.67  thf('79', plain,
% 11.46/11.67      (![X0 : $i]:
% 11.46/11.67         (((k1_mcart_1 @ sk_E_1)
% 11.46/11.67            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 11.46/11.67               (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))))
% 11.46/11.67          | ((k1_mcart_1 @ sk_E_1)
% 11.46/11.67              = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 11.46/11.67                 (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))))
% 11.46/11.67          | ((X0) = (k1_xboole_0)))),
% 11.46/11.67      inference('sup-', [status(thm)], ['49', '78'])).
% 11.46/11.67  thf('80', plain,
% 11.46/11.67      (![X0 : $i]:
% 11.46/11.67         (((X0) = (k1_xboole_0))
% 11.46/11.67          | ((k1_mcart_1 @ sk_E_1)
% 11.46/11.67              = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 11.46/11.67                 (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)))))),
% 11.46/11.67      inference('simplify', [status(thm)], ['79'])).
% 11.46/11.67  thf('81', plain,
% 11.46/11.67      (![X0 : $i]:
% 11.46/11.67         (((X0) = (k1_xboole_0))
% 11.46/11.67          | ((k1_mcart_1 @ sk_E_1)
% 11.46/11.67              = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 11.46/11.67                 (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)))))),
% 11.46/11.67      inference('simplify', [status(thm)], ['79'])).
% 11.46/11.67  thf('82', plain,
% 11.46/11.67      (![X0 : $i, X1 : $i]:
% 11.46/11.67         (((X1) = (X0))
% 11.46/11.67          | ((k1_mcart_1 @ sk_E_1)
% 11.46/11.67              = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 11.46/11.67                 (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))))
% 11.46/11.67          | ((k1_mcart_1 @ sk_E_1)
% 11.46/11.67              = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 11.46/11.67                 (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)))))),
% 11.46/11.67      inference('sup+', [status(thm)], ['80', '81'])).
% 11.46/11.67  thf('83', plain,
% 11.46/11.67      (![X0 : $i, X1 : $i]:
% 11.46/11.67         (((k1_mcart_1 @ sk_E_1)
% 11.46/11.67            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 11.46/11.67               (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))))
% 11.46/11.67          | ((X1) = (X0)))),
% 11.46/11.67      inference('simplify', [status(thm)], ['82'])).
% 11.46/11.67  thf('84', plain,
% 11.46/11.67      (((k1_mcart_1 @ sk_E_1)
% 11.46/11.67         = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 11.46/11.67            (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))))),
% 11.46/11.67      inference('condensation', [status(thm)], ['83'])).
% 11.46/11.67  thf(d3_mcart_1, axiom,
% 11.46/11.67    (![A:$i,B:$i,C:$i]:
% 11.46/11.67     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 11.46/11.67  thf('85', plain,
% 11.46/11.67      (![X24 : $i, X25 : $i, X26 : $i]:
% 11.46/11.67         ((k3_mcart_1 @ X24 @ X25 @ X26)
% 11.46/11.67           = (k4_tarski @ (k4_tarski @ X24 @ X25) @ X26))),
% 11.46/11.67      inference('cnf', [status(esa)], [d3_mcart_1])).
% 11.46/11.67  thf('86', plain,
% 11.46/11.67      (![X0 : $i]:
% 11.46/11.67         ((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 11.46/11.67           (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ X0)
% 11.46/11.67           = (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ X0))),
% 11.46/11.67      inference('sup+', [status(thm)], ['84', '85'])).
% 11.46/11.67  thf('87', plain,
% 11.46/11.67      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 11.46/11.67        | (r2_hidden @ (k1_mcart_1 @ sk_E_1) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 11.46/11.67      inference('sup-', [status(thm)], ['41', '44'])).
% 11.46/11.67  thf('88', plain,
% 11.46/11.67      (![X38 : $i, X39 : $i, X40 : $i]:
% 11.46/11.67         ((r2_hidden @ (k2_mcart_1 @ X38) @ X40)
% 11.46/11.67          | ~ (r2_hidden @ X38 @ (k2_zfmisc_1 @ X39 @ X40)))),
% 11.46/11.67      inference('cnf', [status(esa)], [t10_mcart_1])).
% 11.46/11.67  thf('89', plain,
% 11.46/11.67      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 11.46/11.67        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_2))),
% 11.46/11.67      inference('sup-', [status(thm)], ['87', '88'])).
% 11.46/11.67  thf('90', plain,
% 11.46/11.67      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 11.46/11.67      inference('sup-', [status(thm)], ['5', '6'])).
% 11.46/11.67  thf('91', plain,
% 11.46/11.67      (((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_2)
% 11.46/11.67        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 11.46/11.67      inference('sup-', [status(thm)], ['89', '90'])).
% 11.46/11.67  thf('92', plain,
% 11.46/11.67      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 11.46/11.67         ((k4_zfmisc_1 @ X30 @ X31 @ X32 @ X33)
% 11.46/11.67           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X30 @ X31 @ X32) @ X33))),
% 11.46/11.67      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 11.46/11.67  thf('93', plain,
% 11.46/11.67      (![X0 : $i]:
% 11.46/11.67         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0)
% 11.46/11.67            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 11.46/11.67          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_2))),
% 11.46/11.67      inference('sup+', [status(thm)], ['91', '92'])).
% 11.46/11.67  thf('94', plain,
% 11.46/11.67      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 11.46/11.67      inference('demod', [status(thm)], ['63', '65'])).
% 11.46/11.67  thf('95', plain,
% 11.46/11.67      (![X0 : $i]:
% 11.46/11.67         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0) = (k1_xboole_0))
% 11.46/11.67          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_2))),
% 11.46/11.67      inference('demod', [status(thm)], ['93', '94'])).
% 11.46/11.67  thf('96', plain,
% 11.46/11.67      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 11.46/11.67         (((k4_zfmisc_1 @ X52 @ X53 @ X54 @ X55) != (k1_xboole_0))
% 11.46/11.67          | ((X55) = (k1_xboole_0))
% 11.46/11.67          | ((X54) = (k1_xboole_0))
% 11.46/11.67          | ((X53) = (k1_xboole_0))
% 11.46/11.67          | ((X52) = (k1_xboole_0)))),
% 11.46/11.67      inference('cnf', [status(esa)], [t55_mcart_1])).
% 11.46/11.67  thf('97', plain,
% 11.46/11.67      (![X0 : $i]:
% 11.46/11.67         (((k1_xboole_0) != (k1_xboole_0))
% 11.46/11.67          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_2)
% 11.46/11.67          | ((sk_A) = (k1_xboole_0))
% 11.46/11.67          | ((sk_B_2) = (k1_xboole_0))
% 11.46/11.67          | ((sk_C) = (k1_xboole_0))
% 11.46/11.67          | ((X0) = (k1_xboole_0)))),
% 11.46/11.67      inference('sup-', [status(thm)], ['95', '96'])).
% 11.46/11.67  thf('98', plain,
% 11.46/11.67      (![X0 : $i]:
% 11.46/11.67         (((X0) = (k1_xboole_0))
% 11.46/11.67          | ((sk_C) = (k1_xboole_0))
% 11.46/11.67          | ((sk_B_2) = (k1_xboole_0))
% 11.46/11.67          | ((sk_A) = (k1_xboole_0))
% 11.46/11.67          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_2))),
% 11.46/11.67      inference('simplify', [status(thm)], ['97'])).
% 11.46/11.67  thf('99', plain, (((sk_A) != (k1_xboole_0))),
% 11.46/11.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.46/11.67  thf('100', plain, (((sk_B_2) != (k1_xboole_0))),
% 11.46/11.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.46/11.67  thf('101', plain, (((sk_C) != (k1_xboole_0))),
% 11.46/11.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.46/11.67  thf('102', plain,
% 11.46/11.67      (![X0 : $i]:
% 11.46/11.67         (((X0) = (k1_xboole_0))
% 11.46/11.67          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_2))),
% 11.46/11.67      inference('simplify_reflect-', [status(thm)], ['98', '99', '100', '101'])).
% 11.46/11.67  thf(t1_subset, axiom,
% 11.46/11.67    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 11.46/11.67  thf('103', plain,
% 11.46/11.67      (![X16 : $i, X17 : $i]:
% 11.46/11.67         ((m1_subset_1 @ X16 @ X17) | ~ (r2_hidden @ X16 @ X17))),
% 11.46/11.67      inference('cnf', [status(esa)], [t1_subset])).
% 11.46/11.67  thf('104', plain,
% 11.46/11.67      (![X0 : $i]:
% 11.46/11.67         (((X0) = (k1_xboole_0))
% 11.46/11.67          | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_2))),
% 11.46/11.67      inference('sup-', [status(thm)], ['102', '103'])).
% 11.46/11.67  thf('105', plain,
% 11.46/11.67      (![X0 : $i]:
% 11.46/11.67         (((X0) = (k1_xboole_0))
% 11.46/11.67          | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_2))),
% 11.46/11.67      inference('sup-', [status(thm)], ['102', '103'])).
% 11.46/11.67  thf('106', plain,
% 11.46/11.67      (![X0 : $i, X1 : $i]:
% 11.46/11.67         (((X1) = (X0))
% 11.46/11.67          | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_2)
% 11.46/11.67          | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_2))),
% 11.46/11.67      inference('sup+', [status(thm)], ['104', '105'])).
% 11.46/11.67  thf('107', plain,
% 11.46/11.67      (![X0 : $i, X1 : $i]:
% 11.46/11.67         ((m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_2)
% 11.46/11.67          | ((X1) = (X0)))),
% 11.46/11.67      inference('simplify', [status(thm)], ['106'])).
% 11.46/11.67  thf('108', plain, (((sk_D) != (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_1))),
% 11.46/11.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.46/11.67  thf('109', plain,
% 11.46/11.67      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 11.46/11.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.46/11.67  thf(t50_mcart_1, axiom,
% 11.46/11.67    (![A:$i,B:$i,C:$i]:
% 11.46/11.67     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 11.46/11.67          ( ( C ) != ( k1_xboole_0 ) ) & 
% 11.46/11.67          ( ~( ![D:$i]:
% 11.46/11.67               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 11.46/11.67                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 11.46/11.67                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 11.46/11.67                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 11.46/11.67                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 11.46/11.67                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 11.46/11.67  thf('110', plain,
% 11.46/11.67      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 11.46/11.67         (((X48) = (k1_xboole_0))
% 11.46/11.67          | ((X49) = (k1_xboole_0))
% 11.46/11.67          | ((k5_mcart_1 @ X48 @ X49 @ X51 @ X50)
% 11.46/11.67              = (k1_mcart_1 @ (k1_mcart_1 @ X50)))
% 11.46/11.67          | ~ (m1_subset_1 @ X50 @ (k3_zfmisc_1 @ X48 @ X49 @ X51))
% 11.46/11.67          | ((X51) = (k1_xboole_0)))),
% 11.46/11.67      inference('cnf', [status(esa)], [t50_mcart_1])).
% 11.46/11.67  thf('111', plain,
% 11.46/11.67      ((((sk_C) = (k1_xboole_0))
% 11.46/11.67        | ((k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_1)
% 11.46/11.67            = (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)))
% 11.46/11.67        | ((sk_B_2) = (k1_xboole_0))
% 11.46/11.67        | ((sk_A) = (k1_xboole_0)))),
% 11.46/11.67      inference('sup-', [status(thm)], ['109', '110'])).
% 11.46/11.67  thf('112', plain, (((sk_A) != (k1_xboole_0))),
% 11.46/11.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.46/11.67  thf('113', plain, (((sk_B_2) != (k1_xboole_0))),
% 11.46/11.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.46/11.67  thf('114', plain, (((sk_C) != (k1_xboole_0))),
% 11.46/11.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.46/11.67  thf('115', plain,
% 11.46/11.67      (((k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_1)
% 11.46/11.67         = (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)))),
% 11.46/11.67      inference('simplify_reflect-', [status(thm)],
% 11.46/11.67                ['111', '112', '113', '114'])).
% 11.46/11.67  thf('116', plain, (((sk_D) != (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)))),
% 11.46/11.67      inference('demod', [status(thm)], ['108', '115'])).
% 11.46/11.67  thf('117', plain,
% 11.46/11.67      (![X0 : $i]:
% 11.46/11.67         (((sk_D) != (X0))
% 11.46/11.67          | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_2))),
% 11.46/11.67      inference('sup-', [status(thm)], ['107', '116'])).
% 11.46/11.67  thf('118', plain,
% 11.46/11.67      ((m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_2)),
% 11.46/11.67      inference('simplify', [status(thm)], ['117'])).
% 11.46/11.67  thf('119', plain,
% 11.46/11.67      (![X57 : $i, X58 : $i, X59 : $i]:
% 11.46/11.67         (~ (m1_subset_1 @ X57 @ sk_B_2)
% 11.46/11.67          | ((sk_D) = (X58))
% 11.46/11.67          | ((sk_E_1) != (k3_mcart_1 @ X58 @ X57 @ X59))
% 11.46/11.67          | ~ (m1_subset_1 @ X59 @ sk_C)
% 11.46/11.67          | ~ (m1_subset_1 @ X58 @ sk_A))),
% 11.46/11.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.46/11.67  thf('120', plain,
% 11.46/11.67      (![X0 : $i, X1 : $i]:
% 11.46/11.67         (~ (m1_subset_1 @ X0 @ sk_A)
% 11.46/11.67          | ~ (m1_subset_1 @ X1 @ sk_C)
% 11.46/11.67          | ((sk_E_1)
% 11.46/11.67              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ X1))
% 11.46/11.67          | ((sk_D) = (X0)))),
% 11.46/11.67      inference('sup-', [status(thm)], ['118', '119'])).
% 11.46/11.67  thf('121', plain,
% 11.46/11.67      (![X0 : $i]:
% 11.46/11.67         (((sk_E_1) != (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ X0))
% 11.46/11.67          | ((sk_D) = (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)))
% 11.46/11.67          | ~ (m1_subset_1 @ X0 @ sk_C)
% 11.46/11.67          | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A))),
% 11.46/11.67      inference('sup-', [status(thm)], ['86', '120'])).
% 11.46/11.67  thf('122', plain,
% 11.46/11.67      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 11.46/11.67        | (r2_hidden @ (k1_mcart_1 @ sk_E_1) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 11.46/11.67      inference('sup-', [status(thm)], ['41', '44'])).
% 11.46/11.67  thf('123', plain,
% 11.46/11.67      (![X38 : $i, X39 : $i, X40 : $i]:
% 11.46/11.67         ((r2_hidden @ (k1_mcart_1 @ X38) @ X39)
% 11.46/11.67          | ~ (r2_hidden @ X38 @ (k2_zfmisc_1 @ X39 @ X40)))),
% 11.46/11.67      inference('cnf', [status(esa)], [t10_mcart_1])).
% 11.46/11.67  thf('124', plain,
% 11.46/11.67      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 11.46/11.67        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A))),
% 11.46/11.67      inference('sup-', [status(thm)], ['122', '123'])).
% 11.46/11.67  thf('125', plain,
% 11.46/11.67      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 11.46/11.67      inference('sup-', [status(thm)], ['5', '6'])).
% 11.46/11.67  thf('126', plain,
% 11.46/11.67      (((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A)
% 11.46/11.67        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 11.46/11.67      inference('sup-', [status(thm)], ['124', '125'])).
% 11.46/11.67  thf('127', plain,
% 11.46/11.67      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 11.46/11.67         ((k4_zfmisc_1 @ X30 @ X31 @ X32 @ X33)
% 11.46/11.67           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X30 @ X31 @ X32) @ X33))),
% 11.46/11.67      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 11.46/11.67  thf('128', plain,
% 11.46/11.67      (![X0 : $i]:
% 11.46/11.67         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0)
% 11.46/11.67            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 11.46/11.67          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A))),
% 11.46/11.67      inference('sup+', [status(thm)], ['126', '127'])).
% 11.46/11.67  thf('129', plain,
% 11.46/11.67      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 11.46/11.67      inference('demod', [status(thm)], ['63', '65'])).
% 11.46/11.67  thf('130', plain,
% 11.46/11.67      (![X0 : $i]:
% 11.46/11.67         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0) = (k1_xboole_0))
% 11.46/11.67          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A))),
% 11.46/11.67      inference('demod', [status(thm)], ['128', '129'])).
% 11.46/11.67  thf('131', plain,
% 11.46/11.67      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 11.46/11.67         (((k4_zfmisc_1 @ X52 @ X53 @ X54 @ X55) != (k1_xboole_0))
% 11.46/11.67          | ((X55) = (k1_xboole_0))
% 11.46/11.67          | ((X54) = (k1_xboole_0))
% 11.46/11.67          | ((X53) = (k1_xboole_0))
% 11.46/11.67          | ((X52) = (k1_xboole_0)))),
% 11.46/11.67      inference('cnf', [status(esa)], [t55_mcart_1])).
% 11.46/11.67  thf('132', plain,
% 11.46/11.67      (![X0 : $i]:
% 11.46/11.67         (((k1_xboole_0) != (k1_xboole_0))
% 11.46/11.67          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A)
% 11.46/11.67          | ((sk_A) = (k1_xboole_0))
% 11.46/11.67          | ((sk_B_2) = (k1_xboole_0))
% 11.46/11.67          | ((sk_C) = (k1_xboole_0))
% 11.46/11.67          | ((X0) = (k1_xboole_0)))),
% 11.46/11.67      inference('sup-', [status(thm)], ['130', '131'])).
% 11.46/11.67  thf('133', plain,
% 11.46/11.67      (![X0 : $i]:
% 11.46/11.67         (((X0) = (k1_xboole_0))
% 11.46/11.67          | ((sk_C) = (k1_xboole_0))
% 11.46/11.67          | ((sk_B_2) = (k1_xboole_0))
% 11.46/11.67          | ((sk_A) = (k1_xboole_0))
% 11.46/11.67          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A))),
% 11.46/11.67      inference('simplify', [status(thm)], ['132'])).
% 11.46/11.67  thf('134', plain, (((sk_A) != (k1_xboole_0))),
% 11.46/11.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.46/11.67  thf('135', plain, (((sk_B_2) != (k1_xboole_0))),
% 11.46/11.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.46/11.67  thf('136', plain, (((sk_C) != (k1_xboole_0))),
% 11.46/11.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.46/11.67  thf('137', plain,
% 11.46/11.67      (![X0 : $i]:
% 11.46/11.67         (((X0) = (k1_xboole_0))
% 11.46/11.67          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A))),
% 11.46/11.67      inference('simplify_reflect-', [status(thm)],
% 11.46/11.67                ['133', '134', '135', '136'])).
% 11.46/11.67  thf('138', plain,
% 11.46/11.67      (![X16 : $i, X17 : $i]:
% 11.46/11.67         ((m1_subset_1 @ X16 @ X17) | ~ (r2_hidden @ X16 @ X17))),
% 11.46/11.67      inference('cnf', [status(esa)], [t1_subset])).
% 11.46/11.67  thf('139', plain,
% 11.46/11.67      (![X0 : $i]:
% 11.46/11.67         (((X0) = (k1_xboole_0))
% 11.46/11.67          | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A))),
% 11.46/11.67      inference('sup-', [status(thm)], ['137', '138'])).
% 11.46/11.67  thf('140', plain,
% 11.46/11.67      (![X0 : $i]:
% 11.46/11.67         (((X0) = (k1_xboole_0))
% 11.46/11.67          | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A))),
% 11.46/11.67      inference('sup-', [status(thm)], ['137', '138'])).
% 11.46/11.67  thf('141', plain,
% 11.46/11.67      (![X0 : $i, X1 : $i]:
% 11.46/11.67         (((X1) = (X0))
% 11.46/11.67          | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A)
% 11.46/11.67          | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A))),
% 11.46/11.67      inference('sup+', [status(thm)], ['139', '140'])).
% 11.46/11.67  thf('142', plain,
% 11.46/11.67      (![X0 : $i, X1 : $i]:
% 11.46/11.67         ((m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A)
% 11.46/11.67          | ((X1) = (X0)))),
% 11.46/11.67      inference('simplify', [status(thm)], ['141'])).
% 11.46/11.67  thf('143', plain, (((sk_D) != (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)))),
% 11.46/11.67      inference('demod', [status(thm)], ['108', '115'])).
% 11.46/11.67  thf('144', plain,
% 11.46/11.67      (![X0 : $i]:
% 11.46/11.67         (((sk_D) != (X0))
% 11.46/11.67          | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A))),
% 11.46/11.67      inference('sup-', [status(thm)], ['142', '143'])).
% 11.46/11.67  thf('145', plain,
% 11.46/11.67      ((m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A)),
% 11.46/11.67      inference('simplify', [status(thm)], ['144'])).
% 11.46/11.67  thf('146', plain,
% 11.46/11.67      (![X0 : $i]:
% 11.46/11.67         (((sk_E_1) != (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ X0))
% 11.46/11.67          | ((sk_D) = (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)))
% 11.46/11.67          | ~ (m1_subset_1 @ X0 @ sk_C))),
% 11.46/11.67      inference('demod', [status(thm)], ['121', '145'])).
% 11.46/11.67  thf('147', plain, (((sk_D) != (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)))),
% 11.46/11.67      inference('demod', [status(thm)], ['108', '115'])).
% 11.46/11.67  thf('148', plain,
% 11.46/11.67      (![X0 : $i]:
% 11.46/11.67         (((sk_E_1) != (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ X0))
% 11.46/11.67          | ~ (m1_subset_1 @ X0 @ sk_C))),
% 11.46/11.67      inference('simplify_reflect-', [status(thm)], ['146', '147'])).
% 11.46/11.67  thf('149', plain,
% 11.46/11.67      ((((sk_E_1) != (sk_E_1)) | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E_1) @ sk_C))),
% 11.46/11.67      inference('sup-', [status(thm)], ['40', '148'])).
% 11.46/11.67  thf('150', plain,
% 11.46/11.67      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 11.46/11.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.46/11.67  thf(dt_k7_mcart_1, axiom,
% 11.46/11.67    (![A:$i,B:$i,C:$i,D:$i]:
% 11.46/11.67     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 11.46/11.67       ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ))).
% 11.46/11.67  thf('151', plain,
% 11.46/11.67      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 11.46/11.67         ((m1_subset_1 @ (k7_mcart_1 @ X34 @ X35 @ X36 @ X37) @ X36)
% 11.46/11.67          | ~ (m1_subset_1 @ X37 @ (k3_zfmisc_1 @ X34 @ X35 @ X36)))),
% 11.46/11.67      inference('cnf', [status(esa)], [dt_k7_mcart_1])).
% 11.46/11.67  thf('152', plain,
% 11.46/11.67      ((m1_subset_1 @ (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_1) @ sk_C)),
% 11.46/11.67      inference('sup-', [status(thm)], ['150', '151'])).
% 11.46/11.67  thf('153', plain,
% 11.46/11.67      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 11.46/11.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.46/11.67  thf('154', plain,
% 11.46/11.67      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 11.46/11.67         (((X48) = (k1_xboole_0))
% 11.46/11.67          | ((X49) = (k1_xboole_0))
% 11.46/11.67          | ((k7_mcart_1 @ X48 @ X49 @ X51 @ X50) = (k2_mcart_1 @ X50))
% 11.46/11.67          | ~ (m1_subset_1 @ X50 @ (k3_zfmisc_1 @ X48 @ X49 @ X51))
% 11.46/11.67          | ((X51) = (k1_xboole_0)))),
% 11.46/11.67      inference('cnf', [status(esa)], [t50_mcart_1])).
% 11.46/11.67  thf('155', plain,
% 11.46/11.67      ((((sk_C) = (k1_xboole_0))
% 11.46/11.67        | ((k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_1) = (k2_mcart_1 @ sk_E_1))
% 11.46/11.67        | ((sk_B_2) = (k1_xboole_0))
% 11.46/11.67        | ((sk_A) = (k1_xboole_0)))),
% 11.46/11.67      inference('sup-', [status(thm)], ['153', '154'])).
% 11.46/11.67  thf('156', plain, (((sk_A) != (k1_xboole_0))),
% 11.46/11.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.46/11.67  thf('157', plain, (((sk_B_2) != (k1_xboole_0))),
% 11.46/11.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.46/11.67  thf('158', plain, (((sk_C) != (k1_xboole_0))),
% 11.46/11.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.46/11.67  thf('159', plain,
% 11.46/11.67      (((k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_1) = (k2_mcart_1 @ sk_E_1))),
% 11.46/11.67      inference('simplify_reflect-', [status(thm)],
% 11.46/11.67                ['155', '156', '157', '158'])).
% 11.46/11.67  thf('160', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_E_1) @ sk_C)),
% 11.46/11.67      inference('demod', [status(thm)], ['152', '159'])).
% 11.46/11.67  thf('161', plain, (((sk_E_1) != (sk_E_1))),
% 11.46/11.67      inference('demod', [status(thm)], ['149', '160'])).
% 11.46/11.67  thf('162', plain, ($false), inference('simplify', [status(thm)], ['161'])).
% 11.46/11.67  
% 11.46/11.67  % SZS output end Refutation
% 11.46/11.67  
% 11.46/11.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
