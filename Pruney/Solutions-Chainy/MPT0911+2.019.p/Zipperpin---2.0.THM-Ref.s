%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JNq4IC0XZZ

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:58 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :  245 ( 668 expanded)
%              Number of leaves         :   43 ( 227 expanded)
%              Depth                    :   33
%              Number of atoms          : 2155 (7953 expanded)
%              Number of equality atoms :  244 ( 885 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X34: $i] :
      ( ( X34 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X34 ) @ X34 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('2',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X29 ) @ X30 )
      | ~ ( r2_hidden @ X29 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ),
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
    ! [X34: $i] :
      ( ( X34 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X34 ) @ X34 ) ) ),
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

thf('10',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ X14 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ X14 ) ) ),
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
    ! [X32: $i,X33: $i] :
      ( ( X32
        = ( k4_tarski @ ( k1_mcart_1 @ X32 ) @ ( k2_mcart_1 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X33 )
      | ~ ( r2_hidden @ X32 @ X33 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k3_zfmisc_1 @ X22 @ X23 @ X24 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('16',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k4_zfmisc_1 @ X25 @ X26 @ X27 @ X28 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X25 @ X26 @ X27 ) @ X28 ) ) ),
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
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( ( k4_zfmisc_1 @ X43 @ X44 @ X45 @ X46 )
       != k1_xboole_0 )
      | ( X46 = k1_xboole_0 )
      | ( X45 = k1_xboole_0 )
      | ( X44 = k1_xboole_0 )
      | ( X43 = k1_xboole_0 ) ) ),
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

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('30',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('31',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('32',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 )
      | ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ) ),
    inference(demod,[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X1: $i] :
      ( ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','33'])).

thf('38',plain,(
    ! [X1: $i] :
      ( ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('simplify_reflect+',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k1_xboole_0 != sk_E )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference(eq_fact,[status(thm)],['38'])).

thf('40',plain,(
    ! [X1: $i] :
      ( ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('simplify_reflect+',[status(thm)],['36','37'])).

thf('41',plain,
    ( sk_E
    = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('43',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k3_zfmisc_1 @ X22 @ X23 @ X24 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('44',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X29 ) @ X30 )
      | ~ ( r2_hidden @ X29 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X32: $i,X33: $i] :
      ( ( X32
        = ( k4_tarski @ ( k1_mcart_1 @ X32 ) @ ( k2_mcart_1 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X33 )
      | ~ ( r2_hidden @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('48',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('50',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('51',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_mcart_1 @ X19 @ X20 @ X21 )
      = ( k4_tarski @ ( k4_tarski @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X0 )
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('54',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('55',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X29 ) @ X31 )
      | ~ ( r2_hidden @ X29 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('56',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('61',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ X11 @ X12 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('64',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('65',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ~ ( r1_tarski @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) @ sk_E ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_E )
      | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['53','66'])).

thf('68',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','33'])).

thf('69',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('71',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','33'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
        = ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('76',plain,(
    ! [X43: $i,X44: $i,X45: $i,X47: $i] :
      ( ( X45 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X43 @ X44 @ X45 @ X47 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('77',plain,(
    ! [X43: $i,X44: $i,X47: $i] :
      ( ( k4_zfmisc_1 @ X43 @ X44 @ k1_xboole_0 @ X47 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k3_zfmisc_1 @ X22 @ X23 @ X24 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('79',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k3_zfmisc_1 @ X22 @ X23 @ X24 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k4_zfmisc_1 @ X25 @ X26 @ X27 @ X28 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X25 @ X26 @ X27 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k4_zfmisc_1 @ X25 @ X26 @ X27 @ X28 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X25 @ X26 @ X27 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 @ X4 )
      = ( k2_zfmisc_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) @ X4 ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['77','84'])).

thf('86',plain,(
    ! [X43: $i,X44: $i,X45: $i,X47: $i] :
      ( ( X47 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X43 @ X44 @ X45 @ X47 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('87',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k4_zfmisc_1 @ X43 @ X44 @ X45 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['85','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['75','88'])).

thf('90',plain,(
    ! [X0: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) @ X0 ) )
      | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['74','89'])).

thf('91',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k4_zfmisc_1 @ X25 @ X26 @ X27 @ X28 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X25 @ X26 @ X27 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('92',plain,(
    ! [X0: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 ) )
      | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 )
      | ( k1_xboole_0
        = ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 )
      | ( k1_xboole_0
        = ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 ) )
      | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['69','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 ) )
      | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( ( k4_zfmisc_1 @ X43 @ X44 @ X45 @ X46 )
       != k1_xboole_0 )
      | ( X46 = k1_xboole_0 )
      | ( X45 = k1_xboole_0 )
      | ( X44 = k1_xboole_0 )
      | ( X43 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 )
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
      | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 ) ) ),
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
      | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['98','99','100','101'])).

thf('103',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','33'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('105',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k1_enumset1 @ X4 @ X4 @ X5 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(fc3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ A @ B ) ) )).

thf('106',plain,(
    ! [X9: $i,X10: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc3_xboole_0])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v1_xboole_0 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 ),
    inference('sup-',[status(thm)],['104','107'])).

thf('109',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X48 @ sk_B_2 )
      | ( sk_E
       != ( k3_mcart_1 @ X49 @ X48 @ X50 ) )
      | ( sk_D = X50 )
      | ~ ( m1_subset_1 @ X50 @ sk_C )
      | ~ ( m1_subset_1 @ X49 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_D = X1 )
      | ( sk_E
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','110'])).

thf('112',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('113',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('114',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X29 ) @ X30 )
      | ~ ( r2_hidden @ X29 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('115',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ X11 @ X12 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ~ ( r1_tarski @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) @ sk_E ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_E )
      | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['112','121'])).

thf('123',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','33'])).

thf('124',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
        = ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['75','88'])).

thf('129',plain,(
    ! [X0: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) @ X0 ) )
      | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k4_zfmisc_1 @ X25 @ X26 @ X27 @ X28 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X25 @ X26 @ X27 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('131',plain,(
    ! [X0: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 ) )
      | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
      | ( k1_xboole_0
        = ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
      | ( k1_xboole_0
        = ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 ) )
      | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['124','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 ) )
      | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( ( k4_zfmisc_1 @ X43 @ X44 @ X45 @ X46 )
       != k1_xboole_0 )
      | ( X46 = k1_xboole_0 )
      | ( X45 = k1_xboole_0 )
      | ( X44 = k1_xboole_0 )
      | ( X43 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['137','138','139','140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v1_xboole_0 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('143',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','33'])).

thf('145',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['111','145'])).

thf('147',plain,
    ( ( sk_E != sk_E )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) )
    | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['41','146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('149',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('150',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k3_zfmisc_1 @ X22 @ X23 @ X24 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('151',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X29 ) @ X31 )
      | ~ ( r2_hidden @ X29 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('152',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['149','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('155',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k4_zfmisc_1 @ X25 @ X26 @ X27 @ X28 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X25 @ X26 @ X27 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( ( k4_zfmisc_1 @ X43 @ X44 @ X45 @ X46 )
       != k1_xboole_0 )
      | ( X46 = k1_xboole_0 )
      | ( X45 = k1_xboole_0 )
      | ( X44 = k1_xboole_0 )
      | ( X43 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['159','160','161','162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['148','163'])).

thf('165',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','33'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['166'])).

thf('168',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ X11 @ X12 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v1_xboole_0 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('171',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','33'])).

thf('173',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['171','172'])).

thf('174',plain,
    ( ( sk_E != sk_E )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) )
    | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference(demod,[status(thm)],['147','173'])).

thf('175',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) ) ),
    inference(simplify,[status(thm)],['174'])).

thf('176',plain,(
    sk_D
 != ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
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

thf('178',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( X39 = k1_xboole_0 )
      | ( X40 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X39 @ X40 @ X42 @ X41 )
        = ( k2_mcart_1 @ X41 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k3_zfmisc_1 @ X39 @ X40 @ X42 ) )
      | ( X42 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('179',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E )
      = ( k2_mcart_1 @ sk_E ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['179','180','181','182'])).

thf('184',plain,(
    sk_D
 != ( k2_mcart_1 @ sk_E ) ),
    inference(demod,[status(thm)],['176','183'])).

thf('185',plain,(
    v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['175','184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('187',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k4_zfmisc_1 @ X25 @ X26 @ X27 @ X28 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X25 @ X26 @ X27 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('189',plain,(
    ! [X0: $i] :
      ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['187','188'])).

thf('190',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['85','87'])).

thf('191',plain,(
    ! [X0: $i] :
      ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['189','190'])).

thf('192',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( ( k4_zfmisc_1 @ X43 @ X44 @ X45 @ X46 )
       != k1_xboole_0 )
      | ( X46 = k1_xboole_0 )
      | ( X45 = k1_xboole_0 )
      | ( X44 = k1_xboole_0 )
      | ( X43 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['193'])).

thf('195',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['194','195','196','197'])).

thf('199',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','198'])).

thf('200',plain,(
    $false ),
    inference(simplify,[status(thm)],['199'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JNq4IC0XZZ
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:39:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.35/1.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.35/1.57  % Solved by: fo/fo7.sh
% 1.35/1.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.35/1.57  % done 1775 iterations in 1.108s
% 1.35/1.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.35/1.57  % SZS output start Refutation
% 1.35/1.57  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 1.35/1.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.35/1.57  thf(sk_B_type, type, sk_B: $i > $i).
% 1.35/1.57  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 1.35/1.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.35/1.57  thf(sk_C_type, type, sk_C: $i).
% 1.35/1.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.35/1.57  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 1.35/1.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.35/1.57  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 1.35/1.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.35/1.57  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 1.35/1.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.35/1.57  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 1.35/1.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.35/1.57  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 1.35/1.57  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 1.35/1.57  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.35/1.57  thf(sk_E_type, type, sk_E: $i).
% 1.35/1.57  thf(sk_A_type, type, sk_A: $i).
% 1.35/1.57  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 1.35/1.57  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 1.35/1.57  thf(sk_D_type, type, sk_D: $i).
% 1.35/1.57  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.35/1.57  thf(sk_B_2_type, type, sk_B_2: $i).
% 1.35/1.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.35/1.57  thf(t71_mcart_1, conjecture,
% 1.35/1.57    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.35/1.57     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.35/1.57       ( ( ![F:$i]:
% 1.35/1.57           ( ( m1_subset_1 @ F @ A ) =>
% 1.35/1.57             ( ![G:$i]:
% 1.35/1.57               ( ( m1_subset_1 @ G @ B ) =>
% 1.35/1.57                 ( ![H:$i]:
% 1.35/1.57                   ( ( m1_subset_1 @ H @ C ) =>
% 1.35/1.57                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 1.35/1.57                       ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 1.35/1.57         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.35/1.57           ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.35/1.57           ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 1.35/1.57  thf(zf_stmt_0, negated_conjecture,
% 1.35/1.57    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.35/1.57        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.35/1.57          ( ( ![F:$i]:
% 1.35/1.57              ( ( m1_subset_1 @ F @ A ) =>
% 1.35/1.57                ( ![G:$i]:
% 1.35/1.57                  ( ( m1_subset_1 @ G @ B ) =>
% 1.35/1.57                    ( ![H:$i]:
% 1.35/1.57                      ( ( m1_subset_1 @ H @ C ) =>
% 1.35/1.57                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 1.35/1.57                          ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 1.35/1.57            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.35/1.57              ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.35/1.57              ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 1.35/1.57    inference('cnf.neg', [status(esa)], [t71_mcart_1])).
% 1.35/1.57  thf('0', plain, (((sk_C) != (k1_xboole_0))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf(t34_mcart_1, axiom,
% 1.35/1.57    (![A:$i]:
% 1.35/1.57     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.35/1.57          ( ![B:$i]:
% 1.35/1.57            ( ~( ( r2_hidden @ B @ A ) & 
% 1.35/1.57                 ( ![C:$i,D:$i,E:$i,F:$i]:
% 1.35/1.57                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 1.35/1.57                        ( ( B ) = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) ) ) ) ) ))).
% 1.35/1.57  thf('1', plain,
% 1.35/1.57      (![X34 : $i]:
% 1.35/1.57         (((X34) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X34) @ X34))),
% 1.35/1.57      inference('cnf', [status(esa)], [t34_mcart_1])).
% 1.35/1.57  thf(t10_mcart_1, axiom,
% 1.35/1.57    (![A:$i,B:$i,C:$i]:
% 1.35/1.57     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 1.35/1.57       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 1.35/1.57         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 1.35/1.57  thf('2', plain,
% 1.35/1.57      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.35/1.57         ((r2_hidden @ (k1_mcart_1 @ X29) @ X30)
% 1.35/1.57          | ~ (r2_hidden @ X29 @ (k2_zfmisc_1 @ X30 @ X31)))),
% 1.35/1.57      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.35/1.57  thf('3', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i]:
% 1.35/1.57         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 1.35/1.57          | (r2_hidden @ (k1_mcart_1 @ (sk_B_1 @ (k2_zfmisc_1 @ X1 @ X0))) @ X1))),
% 1.35/1.57      inference('sup-', [status(thm)], ['1', '2'])).
% 1.35/1.57  thf(d1_xboole_0, axiom,
% 1.35/1.57    (![A:$i]:
% 1.35/1.57     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.35/1.57  thf('4', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.35/1.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.35/1.57  thf('5', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i]:
% 1.35/1.57         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.35/1.57      inference('sup-', [status(thm)], ['3', '4'])).
% 1.35/1.57  thf('6', plain,
% 1.35/1.57      (![X34 : $i]:
% 1.35/1.57         (((X34) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X34) @ X34))),
% 1.35/1.57      inference('cnf', [status(esa)], [t34_mcart_1])).
% 1.35/1.57  thf('7', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.35/1.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.35/1.57  thf('8', plain,
% 1.35/1.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.35/1.57      inference('sup-', [status(thm)], ['6', '7'])).
% 1.35/1.57  thf('9', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.57         (((X2) = (k2_zfmisc_1 @ X1 @ X0))
% 1.35/1.57          | ~ (v1_xboole_0 @ X1)
% 1.35/1.57          | ~ (v1_xboole_0 @ X2))),
% 1.35/1.57      inference('sup+', [status(thm)], ['5', '8'])).
% 1.35/1.57  thf('10', plain,
% 1.35/1.57      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf(t2_subset, axiom,
% 1.35/1.57    (![A:$i,B:$i]:
% 1.35/1.57     ( ( m1_subset_1 @ A @ B ) =>
% 1.35/1.57       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 1.35/1.57  thf('11', plain,
% 1.35/1.57      (![X13 : $i, X14 : $i]:
% 1.35/1.57         ((r2_hidden @ X13 @ X14)
% 1.35/1.57          | (v1_xboole_0 @ X14)
% 1.35/1.57          | ~ (m1_subset_1 @ X13 @ X14))),
% 1.35/1.57      inference('cnf', [status(esa)], [t2_subset])).
% 1.35/1.57  thf('12', plain,
% 1.35/1.57      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.35/1.57        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 1.35/1.57      inference('sup-', [status(thm)], ['10', '11'])).
% 1.35/1.57  thf(t23_mcart_1, axiom,
% 1.35/1.57    (![A:$i,B:$i]:
% 1.35/1.57     ( ( v1_relat_1 @ B ) =>
% 1.35/1.57       ( ( r2_hidden @ A @ B ) =>
% 1.35/1.57         ( ( A ) = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ))).
% 1.35/1.57  thf('13', plain,
% 1.35/1.57      (![X32 : $i, X33 : $i]:
% 1.35/1.57         (((X32) = (k4_tarski @ (k1_mcart_1 @ X32) @ (k2_mcart_1 @ X32)))
% 1.35/1.57          | ~ (v1_relat_1 @ X33)
% 1.35/1.57          | ~ (r2_hidden @ X32 @ X33))),
% 1.35/1.57      inference('cnf', [status(esa)], [t23_mcart_1])).
% 1.35/1.57  thf('14', plain,
% 1.35/1.57      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.35/1.57        | ~ (v1_relat_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.35/1.57        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 1.35/1.57      inference('sup-', [status(thm)], ['12', '13'])).
% 1.35/1.57  thf(d3_zfmisc_1, axiom,
% 1.35/1.57    (![A:$i,B:$i,C:$i]:
% 1.35/1.57     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 1.35/1.57       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 1.35/1.57  thf('15', plain,
% 1.35/1.57      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.35/1.57         ((k3_zfmisc_1 @ X22 @ X23 @ X24)
% 1.35/1.57           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23) @ X24))),
% 1.35/1.57      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.35/1.57  thf(fc6_relat_1, axiom,
% 1.35/1.57    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.35/1.57  thf('16', plain,
% 1.35/1.57      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X15 @ X16))),
% 1.35/1.57      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.35/1.57  thf('17', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.57         (v1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))),
% 1.35/1.57      inference('sup+', [status(thm)], ['15', '16'])).
% 1.35/1.57  thf('18', plain,
% 1.35/1.57      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.35/1.57        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 1.35/1.57      inference('demod', [status(thm)], ['14', '17'])).
% 1.35/1.57  thf('19', plain,
% 1.35/1.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.35/1.57      inference('sup-', [status(thm)], ['6', '7'])).
% 1.35/1.57  thf('20', plain,
% 1.35/1.57      ((((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 1.35/1.57        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 1.35/1.57      inference('sup-', [status(thm)], ['18', '19'])).
% 1.35/1.57  thf(d4_zfmisc_1, axiom,
% 1.35/1.57    (![A:$i,B:$i,C:$i,D:$i]:
% 1.35/1.57     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 1.35/1.57       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 1.35/1.57  thf('21', plain,
% 1.35/1.57      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.35/1.57         ((k4_zfmisc_1 @ X25 @ X26 @ X27 @ X28)
% 1.35/1.57           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X25 @ X26 @ X27) @ X28))),
% 1.35/1.57      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.35/1.57  thf('22', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0)
% 1.35/1.57            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 1.35/1.57          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 1.35/1.57      inference('sup+', [status(thm)], ['20', '21'])).
% 1.35/1.57  thf(t55_mcart_1, axiom,
% 1.35/1.57    (![A:$i,B:$i,C:$i,D:$i]:
% 1.35/1.57     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.35/1.57         ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) ) <=>
% 1.35/1.57       ( ( k4_zfmisc_1 @ A @ B @ C @ D ) != ( k1_xboole_0 ) ) ))).
% 1.35/1.57  thf('23', plain,
% 1.35/1.57      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 1.35/1.57         (((k4_zfmisc_1 @ X43 @ X44 @ X45 @ X46) != (k1_xboole_0))
% 1.35/1.57          | ((X46) = (k1_xboole_0))
% 1.35/1.57          | ((X45) = (k1_xboole_0))
% 1.35/1.57          | ((X44) = (k1_xboole_0))
% 1.35/1.57          | ((X43) = (k1_xboole_0)))),
% 1.35/1.57      inference('cnf', [status(esa)], [t55_mcart_1])).
% 1.35/1.57  thf('24', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (((k2_zfmisc_1 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 1.35/1.57          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 1.35/1.57          | ((sk_A) = (k1_xboole_0))
% 1.35/1.57          | ((sk_B_2) = (k1_xboole_0))
% 1.35/1.57          | ((sk_C) = (k1_xboole_0))
% 1.35/1.57          | ((X0) = (k1_xboole_0)))),
% 1.35/1.57      inference('sup-', [status(thm)], ['22', '23'])).
% 1.35/1.57  thf('25', plain, (((sk_C) != (k1_xboole_0))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('26', plain, (((sk_B_2) != (k1_xboole_0))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('27', plain, (((sk_A) != (k1_xboole_0))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('28', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (((k2_zfmisc_1 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 1.35/1.57          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 1.35/1.57          | ((X0) = (k1_xboole_0)))),
% 1.35/1.57      inference('simplify_reflect-', [status(thm)], ['24', '25', '26', '27'])).
% 1.35/1.57  thf('29', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i]:
% 1.35/1.57         (((X0) != (k1_xboole_0))
% 1.35/1.57          | ~ (v1_xboole_0 @ X0)
% 1.35/1.57          | ~ (v1_xboole_0 @ k1_xboole_0)
% 1.35/1.57          | ((X1) = (k1_xboole_0))
% 1.35/1.57          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 1.35/1.57      inference('sup-', [status(thm)], ['9', '28'])).
% 1.35/1.57  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.35/1.57  thf('30', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 1.35/1.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.35/1.57  thf('31', plain,
% 1.35/1.57      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.35/1.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.35/1.57  thf(t7_ordinal1, axiom,
% 1.35/1.57    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.35/1.57  thf('32', plain,
% 1.35/1.57      (![X17 : $i, X18 : $i]:
% 1.35/1.57         (~ (r2_hidden @ X17 @ X18) | ~ (r1_tarski @ X18 @ X17))),
% 1.35/1.57      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.35/1.57  thf('33', plain,
% 1.35/1.57      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 1.35/1.57      inference('sup-', [status(thm)], ['31', '32'])).
% 1.35/1.57  thf('34', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.35/1.57      inference('sup-', [status(thm)], ['30', '33'])).
% 1.35/1.57  thf('35', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i]:
% 1.35/1.57         (((X0) != (k1_xboole_0))
% 1.35/1.57          | ~ (v1_xboole_0 @ X0)
% 1.35/1.57          | ((X1) = (k1_xboole_0))
% 1.35/1.57          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 1.35/1.57      inference('demod', [status(thm)], ['29', '34'])).
% 1.35/1.57  thf('36', plain,
% 1.35/1.57      (![X1 : $i]:
% 1.35/1.57         (((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 1.35/1.57          | ((X1) = (k1_xboole_0))
% 1.35/1.57          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.35/1.57      inference('simplify', [status(thm)], ['35'])).
% 1.35/1.57  thf('37', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.35/1.57      inference('sup-', [status(thm)], ['30', '33'])).
% 1.35/1.57  thf('38', plain,
% 1.35/1.57      (![X1 : $i]:
% 1.35/1.57         (((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 1.35/1.57          | ((X1) = (k1_xboole_0)))),
% 1.35/1.57      inference('simplify_reflect+', [status(thm)], ['36', '37'])).
% 1.35/1.57  thf('39', plain,
% 1.35/1.57      ((((k1_xboole_0) != (sk_E))
% 1.35/1.57        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 1.35/1.57      inference('eq_fact', [status(thm)], ['38'])).
% 1.35/1.57  thf('40', plain,
% 1.35/1.57      (![X1 : $i]:
% 1.35/1.57         (((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 1.35/1.57          | ((X1) = (k1_xboole_0)))),
% 1.35/1.57      inference('simplify_reflect+', [status(thm)], ['36', '37'])).
% 1.35/1.57  thf('41', plain,
% 1.35/1.57      (((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))),
% 1.35/1.57      inference('clc', [status(thm)], ['39', '40'])).
% 1.35/1.57  thf('42', plain,
% 1.35/1.57      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.35/1.57        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 1.35/1.57      inference('sup-', [status(thm)], ['10', '11'])).
% 1.35/1.57  thf('43', plain,
% 1.35/1.57      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.35/1.57         ((k3_zfmisc_1 @ X22 @ X23 @ X24)
% 1.35/1.57           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23) @ X24))),
% 1.35/1.57      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.35/1.57  thf('44', plain,
% 1.35/1.57      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.35/1.57         ((r2_hidden @ (k1_mcart_1 @ X29) @ X30)
% 1.35/1.57          | ~ (r2_hidden @ X29 @ (k2_zfmisc_1 @ X30 @ X31)))),
% 1.35/1.57      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.35/1.57  thf('45', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.35/1.57         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.35/1.57          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 1.35/1.57      inference('sup-', [status(thm)], ['43', '44'])).
% 1.35/1.57  thf('46', plain,
% 1.35/1.57      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.35/1.57        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.35/1.57      inference('sup-', [status(thm)], ['42', '45'])).
% 1.35/1.57  thf('47', plain,
% 1.35/1.57      (![X32 : $i, X33 : $i]:
% 1.35/1.57         (((X32) = (k4_tarski @ (k1_mcart_1 @ X32) @ (k2_mcart_1 @ X32)))
% 1.35/1.57          | ~ (v1_relat_1 @ X33)
% 1.35/1.57          | ~ (r2_hidden @ X32 @ X33))),
% 1.35/1.57      inference('cnf', [status(esa)], [t23_mcart_1])).
% 1.35/1.57  thf('48', plain,
% 1.35/1.57      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.35/1.57        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))
% 1.35/1.57        | ((k1_mcart_1 @ sk_E)
% 1.35/1.57            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 1.35/1.57               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 1.35/1.57      inference('sup-', [status(thm)], ['46', '47'])).
% 1.35/1.57  thf('49', plain,
% 1.35/1.57      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X15 @ X16))),
% 1.35/1.57      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.35/1.57  thf('50', plain,
% 1.35/1.57      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.35/1.57        | ((k1_mcart_1 @ sk_E)
% 1.35/1.57            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 1.35/1.57               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 1.35/1.57      inference('demod', [status(thm)], ['48', '49'])).
% 1.35/1.57  thf(d3_mcart_1, axiom,
% 1.35/1.57    (![A:$i,B:$i,C:$i]:
% 1.35/1.57     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 1.35/1.57  thf('51', plain,
% 1.35/1.57      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.35/1.57         ((k3_mcart_1 @ X19 @ X20 @ X21)
% 1.35/1.57           = (k4_tarski @ (k4_tarski @ X19 @ X20) @ X21))),
% 1.35/1.57      inference('cnf', [status(esa)], [d3_mcart_1])).
% 1.35/1.57  thf('52', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 1.35/1.57            (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X0)
% 1.35/1.57            = (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 1.35/1.57          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 1.35/1.57      inference('sup+', [status(thm)], ['50', '51'])).
% 1.35/1.57  thf('53', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 1.35/1.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.35/1.57  thf('54', plain,
% 1.35/1.57      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.35/1.57        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.35/1.57      inference('sup-', [status(thm)], ['42', '45'])).
% 1.35/1.57  thf('55', plain,
% 1.35/1.57      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.35/1.57         ((r2_hidden @ (k2_mcart_1 @ X29) @ X31)
% 1.35/1.57          | ~ (r2_hidden @ X29 @ (k2_zfmisc_1 @ X30 @ X31)))),
% 1.35/1.57      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.35/1.57  thf('56', plain,
% 1.35/1.57      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.35/1.57        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2))),
% 1.35/1.57      inference('sup-', [status(thm)], ['54', '55'])).
% 1.35/1.57  thf('57', plain,
% 1.35/1.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.35/1.57      inference('sup-', [status(thm)], ['6', '7'])).
% 1.35/1.57  thf('58', plain,
% 1.35/1.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.35/1.57      inference('sup-', [status(thm)], ['6', '7'])).
% 1.35/1.57  thf('59', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i]:
% 1.35/1.57         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 1.35/1.57      inference('sup+', [status(thm)], ['57', '58'])).
% 1.35/1.57  thf('60', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2)
% 1.35/1.57          | ~ (v1_xboole_0 @ X0)
% 1.35/1.57          | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (X0)))),
% 1.35/1.57      inference('sup-', [status(thm)], ['56', '59'])).
% 1.35/1.57  thf(t1_subset, axiom,
% 1.35/1.57    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 1.35/1.57  thf('61', plain,
% 1.35/1.57      (![X11 : $i, X12 : $i]:
% 1.35/1.57         ((m1_subset_1 @ X11 @ X12) | ~ (r2_hidden @ X11 @ X12))),
% 1.35/1.57      inference('cnf', [status(esa)], [t1_subset])).
% 1.35/1.57  thf('62', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (X0))
% 1.35/1.57          | ~ (v1_xboole_0 @ X0)
% 1.35/1.57          | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2))),
% 1.35/1.57      inference('sup-', [status(thm)], ['60', '61'])).
% 1.35/1.57  thf('63', plain,
% 1.35/1.57      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.35/1.57        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 1.35/1.57      inference('sup-', [status(thm)], ['10', '11'])).
% 1.35/1.57  thf('64', plain,
% 1.35/1.57      (![X17 : $i, X18 : $i]:
% 1.35/1.57         (~ (r2_hidden @ X17 @ X18) | ~ (r1_tarski @ X18 @ X17))),
% 1.35/1.57      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.35/1.57  thf('65', plain,
% 1.35/1.57      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.35/1.57        | ~ (r1_tarski @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) @ sk_E))),
% 1.35/1.57      inference('sup-', [status(thm)], ['63', '64'])).
% 1.35/1.57  thf('66', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (~ (r1_tarski @ X0 @ sk_E)
% 1.35/1.57          | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2)
% 1.35/1.57          | ~ (v1_xboole_0 @ X0)
% 1.35/1.57          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 1.35/1.57      inference('sup-', [status(thm)], ['62', '65'])).
% 1.35/1.57  thf('67', plain,
% 1.35/1.57      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.35/1.57        | ~ (v1_xboole_0 @ k1_xboole_0)
% 1.35/1.57        | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2))),
% 1.35/1.57      inference('sup-', [status(thm)], ['53', '66'])).
% 1.35/1.57  thf('68', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.35/1.57      inference('sup-', [status(thm)], ['30', '33'])).
% 1.35/1.57  thf('69', plain,
% 1.35/1.57      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.35/1.57        | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2))),
% 1.35/1.57      inference('demod', [status(thm)], ['67', '68'])).
% 1.35/1.57  thf('70', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i]:
% 1.35/1.57         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.35/1.57      inference('sup-', [status(thm)], ['3', '4'])).
% 1.35/1.57  thf('71', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.35/1.57      inference('sup-', [status(thm)], ['30', '33'])).
% 1.35/1.57  thf('72', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i]:
% 1.35/1.57         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X1))),
% 1.35/1.57      inference('sup+', [status(thm)], ['70', '71'])).
% 1.35/1.57  thf('73', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (X0))
% 1.35/1.57          | ~ (v1_xboole_0 @ X0)
% 1.35/1.57          | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2))),
% 1.35/1.57      inference('sup-', [status(thm)], ['60', '61'])).
% 1.35/1.57  thf('74', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i]:
% 1.35/1.57         (~ (v1_xboole_0 @ X1)
% 1.35/1.57          | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2)
% 1.35/1.57          | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k2_zfmisc_1 @ X1 @ X0)))),
% 1.35/1.57      inference('sup-', [status(thm)], ['72', '73'])).
% 1.35/1.57  thf('75', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i]:
% 1.35/1.57         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.35/1.57      inference('sup-', [status(thm)], ['3', '4'])).
% 1.35/1.57  thf('76', plain,
% 1.35/1.57      (![X43 : $i, X44 : $i, X45 : $i, X47 : $i]:
% 1.35/1.57         (((X45) != (k1_xboole_0))
% 1.35/1.57          | ((k4_zfmisc_1 @ X43 @ X44 @ X45 @ X47) = (k1_xboole_0)))),
% 1.35/1.57      inference('cnf', [status(esa)], [t55_mcart_1])).
% 1.35/1.57  thf('77', plain,
% 1.35/1.57      (![X43 : $i, X44 : $i, X47 : $i]:
% 1.35/1.57         ((k4_zfmisc_1 @ X43 @ X44 @ k1_xboole_0 @ X47) = (k1_xboole_0))),
% 1.35/1.57      inference('simplify', [status(thm)], ['76'])).
% 1.35/1.57  thf('78', plain,
% 1.35/1.57      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.35/1.57         ((k3_zfmisc_1 @ X22 @ X23 @ X24)
% 1.35/1.57           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23) @ X24))),
% 1.35/1.57      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.35/1.57  thf('79', plain,
% 1.35/1.57      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.35/1.57         ((k3_zfmisc_1 @ X22 @ X23 @ X24)
% 1.35/1.57           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23) @ X24))),
% 1.35/1.57      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.35/1.57  thf('80', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.35/1.57         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 1.35/1.57           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 1.35/1.57      inference('sup+', [status(thm)], ['78', '79'])).
% 1.35/1.57  thf('81', plain,
% 1.35/1.57      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.35/1.57         ((k4_zfmisc_1 @ X25 @ X26 @ X27 @ X28)
% 1.35/1.57           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X25 @ X26 @ X27) @ X28))),
% 1.35/1.57      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.35/1.57  thf('82', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.35/1.57         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 1.35/1.57           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 1.35/1.57      inference('demod', [status(thm)], ['80', '81'])).
% 1.35/1.57  thf('83', plain,
% 1.35/1.57      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.35/1.57         ((k4_zfmisc_1 @ X25 @ X26 @ X27 @ X28)
% 1.35/1.57           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X25 @ X26 @ X27) @ X28))),
% 1.35/1.57      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.35/1.57  thf('84', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.35/1.57         ((k4_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0 @ X4)
% 1.35/1.57           = (k2_zfmisc_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) @ X4))),
% 1.35/1.57      inference('sup+', [status(thm)], ['82', '83'])).
% 1.35/1.57  thf('85', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.35/1.57         ((k1_xboole_0)
% 1.35/1.57           = (k2_zfmisc_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ k1_xboole_0) @ X0))),
% 1.35/1.57      inference('sup+', [status(thm)], ['77', '84'])).
% 1.35/1.57  thf('86', plain,
% 1.35/1.57      (![X43 : $i, X44 : $i, X45 : $i, X47 : $i]:
% 1.35/1.57         (((X47) != (k1_xboole_0))
% 1.35/1.57          | ((k4_zfmisc_1 @ X43 @ X44 @ X45 @ X47) = (k1_xboole_0)))),
% 1.35/1.57      inference('cnf', [status(esa)], [t55_mcart_1])).
% 1.35/1.57  thf('87', plain,
% 1.35/1.57      (![X43 : $i, X44 : $i, X45 : $i]:
% 1.35/1.57         ((k4_zfmisc_1 @ X43 @ X44 @ X45 @ k1_xboole_0) = (k1_xboole_0))),
% 1.35/1.57      inference('simplify', [status(thm)], ['86'])).
% 1.35/1.57  thf('88', plain,
% 1.35/1.57      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 1.35/1.57      inference('demod', [status(thm)], ['85', '87'])).
% 1.35/1.57  thf('89', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.57         (((k1_xboole_0) = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X2))
% 1.35/1.57          | ~ (v1_xboole_0 @ X1))),
% 1.35/1.57      inference('sup+', [status(thm)], ['75', '88'])).
% 1.35/1.57  thf('90', plain,
% 1.35/1.57      (![X0 : $i, X2 : $i]:
% 1.35/1.57         (((k1_xboole_0)
% 1.35/1.57            = (k2_zfmisc_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) @ X0))
% 1.35/1.57          | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2)
% 1.35/1.57          | ~ (v1_xboole_0 @ X2)
% 1.35/1.57          | ~ (v1_xboole_0 @ X2))),
% 1.35/1.57      inference('sup+', [status(thm)], ['74', '89'])).
% 1.35/1.57  thf('91', plain,
% 1.35/1.57      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.35/1.57         ((k4_zfmisc_1 @ X25 @ X26 @ X27 @ X28)
% 1.35/1.57           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X25 @ X26 @ X27) @ X28))),
% 1.35/1.57      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.35/1.57  thf('92', plain,
% 1.35/1.57      (![X0 : $i, X2 : $i]:
% 1.35/1.57         (((k1_xboole_0) = (k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0))
% 1.35/1.57          | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2)
% 1.35/1.57          | ~ (v1_xboole_0 @ X2)
% 1.35/1.57          | ~ (v1_xboole_0 @ X2))),
% 1.35/1.57      inference('demod', [status(thm)], ['90', '91'])).
% 1.35/1.57  thf('93', plain,
% 1.35/1.57      (![X0 : $i, X2 : $i]:
% 1.35/1.57         (~ (v1_xboole_0 @ X2)
% 1.35/1.57          | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2)
% 1.35/1.57          | ((k1_xboole_0) = (k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0)))),
% 1.35/1.57      inference('simplify', [status(thm)], ['92'])).
% 1.35/1.57  thf('94', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         ((m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2)
% 1.35/1.57          | ((k1_xboole_0) = (k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0))
% 1.35/1.57          | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2))),
% 1.35/1.57      inference('sup-', [status(thm)], ['69', '93'])).
% 1.35/1.57  thf('95', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (((k1_xboole_0) = (k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0))
% 1.35/1.57          | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2))),
% 1.35/1.57      inference('simplify', [status(thm)], ['94'])).
% 1.35/1.57  thf('96', plain,
% 1.35/1.57      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 1.35/1.57         (((k4_zfmisc_1 @ X43 @ X44 @ X45 @ X46) != (k1_xboole_0))
% 1.35/1.57          | ((X46) = (k1_xboole_0))
% 1.35/1.57          | ((X45) = (k1_xboole_0))
% 1.35/1.57          | ((X44) = (k1_xboole_0))
% 1.35/1.57          | ((X43) = (k1_xboole_0)))),
% 1.35/1.57      inference('cnf', [status(esa)], [t55_mcart_1])).
% 1.35/1.57  thf('97', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (((k1_xboole_0) != (k1_xboole_0))
% 1.35/1.57          | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2)
% 1.35/1.57          | ((sk_A) = (k1_xboole_0))
% 1.35/1.57          | ((sk_B_2) = (k1_xboole_0))
% 1.35/1.57          | ((sk_C) = (k1_xboole_0))
% 1.35/1.57          | ((X0) = (k1_xboole_0)))),
% 1.35/1.57      inference('sup-', [status(thm)], ['95', '96'])).
% 1.35/1.57  thf('98', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (((X0) = (k1_xboole_0))
% 1.35/1.57          | ((sk_C) = (k1_xboole_0))
% 1.35/1.57          | ((sk_B_2) = (k1_xboole_0))
% 1.35/1.57          | ((sk_A) = (k1_xboole_0))
% 1.35/1.57          | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2))),
% 1.35/1.57      inference('simplify', [status(thm)], ['97'])).
% 1.35/1.57  thf('99', plain, (((sk_A) != (k1_xboole_0))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('100', plain, (((sk_B_2) != (k1_xboole_0))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('101', plain, (((sk_C) != (k1_xboole_0))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('102', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (((X0) = (k1_xboole_0))
% 1.35/1.57          | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2))),
% 1.35/1.57      inference('simplify_reflect-', [status(thm)], ['98', '99', '100', '101'])).
% 1.35/1.57  thf('103', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.35/1.57      inference('sup-', [status(thm)], ['30', '33'])).
% 1.35/1.57  thf('104', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         ((v1_xboole_0 @ X0)
% 1.35/1.57          | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2))),
% 1.35/1.57      inference('sup+', [status(thm)], ['102', '103'])).
% 1.35/1.57  thf(t70_enumset1, axiom,
% 1.35/1.57    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.35/1.57  thf('105', plain,
% 1.35/1.57      (![X4 : $i, X5 : $i]:
% 1.35/1.57         ((k1_enumset1 @ X4 @ X4 @ X5) = (k2_tarski @ X4 @ X5))),
% 1.35/1.57      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.35/1.57  thf(fc3_xboole_0, axiom,
% 1.35/1.57    (![A:$i,B:$i]: ( ~( v1_xboole_0 @ ( k2_tarski @ A @ B ) ) ))).
% 1.35/1.57  thf('106', plain,
% 1.35/1.57      (![X9 : $i, X10 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X9 @ X10))),
% 1.35/1.57      inference('cnf', [status(esa)], [fc3_xboole_0])).
% 1.35/1.57  thf('107', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i]: ~ (v1_xboole_0 @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 1.35/1.57      inference('sup-', [status(thm)], ['105', '106'])).
% 1.35/1.57  thf('108', plain,
% 1.35/1.57      ((m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2)),
% 1.35/1.57      inference('sup-', [status(thm)], ['104', '107'])).
% 1.35/1.57  thf('109', plain,
% 1.35/1.57      (![X48 : $i, X49 : $i, X50 : $i]:
% 1.35/1.57         (~ (m1_subset_1 @ X48 @ sk_B_2)
% 1.35/1.57          | ((sk_E) != (k3_mcart_1 @ X49 @ X48 @ X50))
% 1.35/1.57          | ((sk_D) = (X50))
% 1.35/1.57          | ~ (m1_subset_1 @ X50 @ sk_C)
% 1.35/1.57          | ~ (m1_subset_1 @ X49 @ sk_A))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('110', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i]:
% 1.35/1.57         (~ (m1_subset_1 @ X0 @ sk_A)
% 1.35/1.57          | ~ (m1_subset_1 @ X1 @ sk_C)
% 1.35/1.57          | ((sk_D) = (X1))
% 1.35/1.57          | ((sk_E)
% 1.35/1.57              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1)))),
% 1.35/1.57      inference('sup-', [status(thm)], ['108', '109'])).
% 1.35/1.57  thf('111', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 1.35/1.57          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.35/1.57          | ((sk_D) = (X0))
% 1.35/1.57          | ~ (m1_subset_1 @ X0 @ sk_C)
% 1.35/1.57          | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 1.35/1.57      inference('sup-', [status(thm)], ['52', '110'])).
% 1.35/1.57  thf('112', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 1.35/1.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.35/1.57  thf('113', plain,
% 1.35/1.57      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.35/1.57        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.35/1.57      inference('sup-', [status(thm)], ['42', '45'])).
% 1.35/1.57  thf('114', plain,
% 1.35/1.57      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.35/1.57         ((r2_hidden @ (k1_mcart_1 @ X29) @ X30)
% 1.35/1.57          | ~ (r2_hidden @ X29 @ (k2_zfmisc_1 @ X30 @ X31)))),
% 1.35/1.57      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.35/1.57  thf('115', plain,
% 1.35/1.57      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.35/1.57        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 1.35/1.57      inference('sup-', [status(thm)], ['113', '114'])).
% 1.35/1.57  thf('116', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i]:
% 1.35/1.57         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 1.35/1.57      inference('sup+', [status(thm)], ['57', '58'])).
% 1.35/1.57  thf('117', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 1.35/1.57          | ~ (v1_xboole_0 @ X0)
% 1.35/1.57          | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (X0)))),
% 1.35/1.57      inference('sup-', [status(thm)], ['115', '116'])).
% 1.35/1.57  thf('118', plain,
% 1.35/1.57      (![X11 : $i, X12 : $i]:
% 1.35/1.57         ((m1_subset_1 @ X11 @ X12) | ~ (r2_hidden @ X11 @ X12))),
% 1.35/1.57      inference('cnf', [status(esa)], [t1_subset])).
% 1.35/1.57  thf('119', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (X0))
% 1.35/1.57          | ~ (v1_xboole_0 @ X0)
% 1.35/1.57          | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 1.35/1.57      inference('sup-', [status(thm)], ['117', '118'])).
% 1.35/1.57  thf('120', plain,
% 1.35/1.57      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.35/1.57        | ~ (r1_tarski @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) @ sk_E))),
% 1.35/1.57      inference('sup-', [status(thm)], ['63', '64'])).
% 1.35/1.57  thf('121', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (~ (r1_tarski @ X0 @ sk_E)
% 1.35/1.57          | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 1.35/1.57          | ~ (v1_xboole_0 @ X0)
% 1.35/1.57          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 1.35/1.57      inference('sup-', [status(thm)], ['119', '120'])).
% 1.35/1.57  thf('122', plain,
% 1.35/1.57      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.35/1.57        | ~ (v1_xboole_0 @ k1_xboole_0)
% 1.35/1.57        | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 1.35/1.57      inference('sup-', [status(thm)], ['112', '121'])).
% 1.35/1.57  thf('123', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.35/1.57      inference('sup-', [status(thm)], ['30', '33'])).
% 1.35/1.57  thf('124', plain,
% 1.35/1.57      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.35/1.57        | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 1.35/1.57      inference('demod', [status(thm)], ['122', '123'])).
% 1.35/1.57  thf('125', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i]:
% 1.35/1.57         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X1))),
% 1.35/1.57      inference('sup+', [status(thm)], ['70', '71'])).
% 1.35/1.57  thf('126', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (X0))
% 1.35/1.57          | ~ (v1_xboole_0 @ X0)
% 1.35/1.57          | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 1.35/1.57      inference('sup-', [status(thm)], ['117', '118'])).
% 1.35/1.57  thf('127', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i]:
% 1.35/1.57         (~ (v1_xboole_0 @ X1)
% 1.35/1.57          | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 1.35/1.57          | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k2_zfmisc_1 @ X1 @ X0)))),
% 1.35/1.57      inference('sup-', [status(thm)], ['125', '126'])).
% 1.35/1.57  thf('128', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.57         (((k1_xboole_0) = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X2))
% 1.35/1.57          | ~ (v1_xboole_0 @ X1))),
% 1.35/1.57      inference('sup+', [status(thm)], ['75', '88'])).
% 1.35/1.57  thf('129', plain,
% 1.35/1.57      (![X0 : $i, X2 : $i]:
% 1.35/1.57         (((k1_xboole_0)
% 1.35/1.57            = (k2_zfmisc_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) @ X0))
% 1.35/1.57          | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 1.35/1.57          | ~ (v1_xboole_0 @ X2)
% 1.35/1.57          | ~ (v1_xboole_0 @ X2))),
% 1.35/1.57      inference('sup+', [status(thm)], ['127', '128'])).
% 1.35/1.57  thf('130', plain,
% 1.35/1.57      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.35/1.57         ((k4_zfmisc_1 @ X25 @ X26 @ X27 @ X28)
% 1.35/1.57           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X25 @ X26 @ X27) @ X28))),
% 1.35/1.57      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.35/1.57  thf('131', plain,
% 1.35/1.57      (![X0 : $i, X2 : $i]:
% 1.35/1.57         (((k1_xboole_0) = (k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0))
% 1.35/1.57          | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 1.35/1.57          | ~ (v1_xboole_0 @ X2)
% 1.35/1.57          | ~ (v1_xboole_0 @ X2))),
% 1.35/1.57      inference('demod', [status(thm)], ['129', '130'])).
% 1.35/1.57  thf('132', plain,
% 1.35/1.57      (![X0 : $i, X2 : $i]:
% 1.35/1.57         (~ (v1_xboole_0 @ X2)
% 1.35/1.57          | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 1.35/1.57          | ((k1_xboole_0) = (k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0)))),
% 1.35/1.57      inference('simplify', [status(thm)], ['131'])).
% 1.35/1.57  thf('133', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         ((m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 1.35/1.57          | ((k1_xboole_0) = (k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0))
% 1.35/1.57          | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 1.35/1.57      inference('sup-', [status(thm)], ['124', '132'])).
% 1.35/1.57  thf('134', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (((k1_xboole_0) = (k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0))
% 1.35/1.57          | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 1.35/1.57      inference('simplify', [status(thm)], ['133'])).
% 1.35/1.57  thf('135', plain,
% 1.35/1.57      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 1.35/1.57         (((k4_zfmisc_1 @ X43 @ X44 @ X45 @ X46) != (k1_xboole_0))
% 1.35/1.57          | ((X46) = (k1_xboole_0))
% 1.35/1.57          | ((X45) = (k1_xboole_0))
% 1.35/1.57          | ((X44) = (k1_xboole_0))
% 1.35/1.57          | ((X43) = (k1_xboole_0)))),
% 1.35/1.57      inference('cnf', [status(esa)], [t55_mcart_1])).
% 1.35/1.57  thf('136', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (((k1_xboole_0) != (k1_xboole_0))
% 1.35/1.57          | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 1.35/1.57          | ((sk_A) = (k1_xboole_0))
% 1.35/1.57          | ((sk_B_2) = (k1_xboole_0))
% 1.35/1.57          | ((sk_C) = (k1_xboole_0))
% 1.35/1.57          | ((X0) = (k1_xboole_0)))),
% 1.35/1.57      inference('sup-', [status(thm)], ['134', '135'])).
% 1.35/1.57  thf('137', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (((X0) = (k1_xboole_0))
% 1.35/1.57          | ((sk_C) = (k1_xboole_0))
% 1.35/1.57          | ((sk_B_2) = (k1_xboole_0))
% 1.35/1.57          | ((sk_A) = (k1_xboole_0))
% 1.35/1.57          | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 1.35/1.57      inference('simplify', [status(thm)], ['136'])).
% 1.35/1.57  thf('138', plain, (((sk_A) != (k1_xboole_0))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('139', plain, (((sk_B_2) != (k1_xboole_0))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('140', plain, (((sk_C) != (k1_xboole_0))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('141', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (((X0) = (k1_xboole_0))
% 1.35/1.57          | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 1.35/1.57      inference('simplify_reflect-', [status(thm)],
% 1.35/1.57                ['137', '138', '139', '140'])).
% 1.35/1.57  thf('142', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i]: ~ (v1_xboole_0 @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 1.35/1.57      inference('sup-', [status(thm)], ['105', '106'])).
% 1.35/1.57  thf('143', plain,
% 1.35/1.57      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.35/1.57        | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 1.35/1.57      inference('sup-', [status(thm)], ['141', '142'])).
% 1.35/1.57  thf('144', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.35/1.57      inference('sup-', [status(thm)], ['30', '33'])).
% 1.35/1.57  thf('145', plain,
% 1.35/1.57      ((m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)),
% 1.35/1.57      inference('demod', [status(thm)], ['143', '144'])).
% 1.35/1.57  thf('146', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 1.35/1.57          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.35/1.57          | ((sk_D) = (X0))
% 1.35/1.57          | ~ (m1_subset_1 @ X0 @ sk_C))),
% 1.35/1.57      inference('demod', [status(thm)], ['111', '145'])).
% 1.35/1.57  thf('147', plain,
% 1.35/1.57      ((((sk_E) != (sk_E))
% 1.35/1.57        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)
% 1.35/1.57        | ((sk_D) = (k2_mcart_1 @ sk_E))
% 1.35/1.57        | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 1.35/1.57      inference('sup-', [status(thm)], ['41', '146'])).
% 1.35/1.57  thf('148', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i]:
% 1.35/1.57         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.35/1.57      inference('sup-', [status(thm)], ['3', '4'])).
% 1.35/1.57  thf('149', plain,
% 1.35/1.57      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.35/1.57        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 1.35/1.57      inference('sup-', [status(thm)], ['10', '11'])).
% 1.35/1.57  thf('150', plain,
% 1.35/1.57      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.35/1.57         ((k3_zfmisc_1 @ X22 @ X23 @ X24)
% 1.35/1.57           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23) @ X24))),
% 1.35/1.57      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.35/1.57  thf('151', plain,
% 1.35/1.57      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.35/1.57         ((r2_hidden @ (k2_mcart_1 @ X29) @ X31)
% 1.35/1.57          | ~ (r2_hidden @ X29 @ (k2_zfmisc_1 @ X30 @ X31)))),
% 1.35/1.57      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.35/1.57  thf('152', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.35/1.57         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.35/1.57          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 1.35/1.57      inference('sup-', [status(thm)], ['150', '151'])).
% 1.35/1.57  thf('153', plain,
% 1.35/1.57      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.35/1.57        | (r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C))),
% 1.35/1.57      inference('sup-', [status(thm)], ['149', '152'])).
% 1.35/1.57  thf('154', plain,
% 1.35/1.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.35/1.57      inference('sup-', [status(thm)], ['6', '7'])).
% 1.35/1.57  thf('155', plain,
% 1.35/1.57      (((r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C)
% 1.35/1.57        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 1.35/1.57      inference('sup-', [status(thm)], ['153', '154'])).
% 1.35/1.57  thf('156', plain,
% 1.35/1.57      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.35/1.57         ((k4_zfmisc_1 @ X25 @ X26 @ X27 @ X28)
% 1.35/1.57           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X25 @ X26 @ X27) @ X28))),
% 1.35/1.57      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.35/1.57  thf('157', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0)
% 1.35/1.57            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 1.35/1.57          | (r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C))),
% 1.35/1.57      inference('sup+', [status(thm)], ['155', '156'])).
% 1.35/1.57  thf('158', plain,
% 1.35/1.57      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 1.35/1.57         (((k4_zfmisc_1 @ X43 @ X44 @ X45 @ X46) != (k1_xboole_0))
% 1.35/1.57          | ((X46) = (k1_xboole_0))
% 1.35/1.57          | ((X45) = (k1_xboole_0))
% 1.35/1.57          | ((X44) = (k1_xboole_0))
% 1.35/1.57          | ((X43) = (k1_xboole_0)))),
% 1.35/1.57      inference('cnf', [status(esa)], [t55_mcart_1])).
% 1.35/1.57  thf('159', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (((k2_zfmisc_1 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 1.35/1.57          | (r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C)
% 1.35/1.57          | ((sk_A) = (k1_xboole_0))
% 1.35/1.57          | ((sk_B_2) = (k1_xboole_0))
% 1.35/1.57          | ((sk_C) = (k1_xboole_0))
% 1.35/1.57          | ((X0) = (k1_xboole_0)))),
% 1.35/1.57      inference('sup-', [status(thm)], ['157', '158'])).
% 1.35/1.57  thf('160', plain, (((sk_C) != (k1_xboole_0))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('161', plain, (((sk_B_2) != (k1_xboole_0))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('162', plain, (((sk_A) != (k1_xboole_0))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('163', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (((k2_zfmisc_1 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 1.35/1.57          | (r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C)
% 1.35/1.57          | ((X0) = (k1_xboole_0)))),
% 1.35/1.57      inference('simplify_reflect-', [status(thm)],
% 1.35/1.57                ['159', '160', '161', '162'])).
% 1.35/1.57  thf('164', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (((k1_xboole_0) != (k1_xboole_0))
% 1.35/1.57          | ~ (v1_xboole_0 @ k1_xboole_0)
% 1.35/1.57          | ((X0) = (k1_xboole_0))
% 1.35/1.57          | (r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C))),
% 1.35/1.57      inference('sup-', [status(thm)], ['148', '163'])).
% 1.35/1.57  thf('165', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.35/1.57      inference('sup-', [status(thm)], ['30', '33'])).
% 1.35/1.57  thf('166', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (((k1_xboole_0) != (k1_xboole_0))
% 1.35/1.57          | ((X0) = (k1_xboole_0))
% 1.35/1.57          | (r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C))),
% 1.35/1.57      inference('demod', [status(thm)], ['164', '165'])).
% 1.35/1.57  thf('167', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         ((r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C) | ((X0) = (k1_xboole_0)))),
% 1.35/1.57      inference('simplify', [status(thm)], ['166'])).
% 1.35/1.57  thf('168', plain,
% 1.35/1.57      (![X11 : $i, X12 : $i]:
% 1.35/1.57         ((m1_subset_1 @ X11 @ X12) | ~ (r2_hidden @ X11 @ X12))),
% 1.35/1.57      inference('cnf', [status(esa)], [t1_subset])).
% 1.35/1.57  thf('169', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (((X0) = (k1_xboole_0)) | (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C))),
% 1.35/1.57      inference('sup-', [status(thm)], ['167', '168'])).
% 1.35/1.57  thf('170', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i]: ~ (v1_xboole_0 @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 1.35/1.57      inference('sup-', [status(thm)], ['105', '106'])).
% 1.35/1.57  thf('171', plain,
% 1.35/1.57      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.35/1.57        | (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C))),
% 1.35/1.57      inference('sup-', [status(thm)], ['169', '170'])).
% 1.35/1.57  thf('172', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.35/1.57      inference('sup-', [status(thm)], ['30', '33'])).
% 1.35/1.57  thf('173', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)),
% 1.35/1.57      inference('demod', [status(thm)], ['171', '172'])).
% 1.35/1.57  thf('174', plain,
% 1.35/1.57      ((((sk_E) != (sk_E))
% 1.35/1.57        | ((sk_D) = (k2_mcart_1 @ sk_E))
% 1.35/1.57        | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 1.35/1.57      inference('demod', [status(thm)], ['147', '173'])).
% 1.35/1.57  thf('175', plain,
% 1.35/1.57      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 1.35/1.57        | ((sk_D) = (k2_mcart_1 @ sk_E)))),
% 1.35/1.57      inference('simplify', [status(thm)], ['174'])).
% 1.35/1.57  thf('176', plain, (((sk_D) != (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('177', plain,
% 1.35/1.57      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf(t50_mcart_1, axiom,
% 1.35/1.57    (![A:$i,B:$i,C:$i]:
% 1.35/1.57     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.35/1.57          ( ( C ) != ( k1_xboole_0 ) ) & 
% 1.35/1.57          ( ~( ![D:$i]:
% 1.35/1.57               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.35/1.57                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 1.35/1.57                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 1.35/1.57                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 1.35/1.57                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 1.35/1.57                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 1.35/1.57  thf('178', plain,
% 1.35/1.57      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 1.35/1.57         (((X39) = (k1_xboole_0))
% 1.35/1.57          | ((X40) = (k1_xboole_0))
% 1.35/1.57          | ((k7_mcart_1 @ X39 @ X40 @ X42 @ X41) = (k2_mcart_1 @ X41))
% 1.35/1.57          | ~ (m1_subset_1 @ X41 @ (k3_zfmisc_1 @ X39 @ X40 @ X42))
% 1.35/1.57          | ((X42) = (k1_xboole_0)))),
% 1.35/1.57      inference('cnf', [status(esa)], [t50_mcart_1])).
% 1.35/1.57  thf('179', plain,
% 1.35/1.57      ((((sk_C) = (k1_xboole_0))
% 1.35/1.57        | ((k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))
% 1.35/1.57        | ((sk_B_2) = (k1_xboole_0))
% 1.35/1.57        | ((sk_A) = (k1_xboole_0)))),
% 1.35/1.57      inference('sup-', [status(thm)], ['177', '178'])).
% 1.35/1.57  thf('180', plain, (((sk_A) != (k1_xboole_0))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('181', plain, (((sk_B_2) != (k1_xboole_0))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('182', plain, (((sk_C) != (k1_xboole_0))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('183', plain,
% 1.35/1.57      (((k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))),
% 1.35/1.57      inference('simplify_reflect-', [status(thm)],
% 1.35/1.57                ['179', '180', '181', '182'])).
% 1.35/1.57  thf('184', plain, (((sk_D) != (k2_mcart_1 @ sk_E))),
% 1.35/1.57      inference('demod', [status(thm)], ['176', '183'])).
% 1.35/1.57  thf('185', plain, ((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 1.35/1.57      inference('simplify_reflect-', [status(thm)], ['175', '184'])).
% 1.35/1.57  thf('186', plain,
% 1.35/1.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.35/1.57      inference('sup-', [status(thm)], ['6', '7'])).
% 1.35/1.57  thf('187', plain, (((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0))),
% 1.35/1.57      inference('sup-', [status(thm)], ['185', '186'])).
% 1.35/1.57  thf('188', plain,
% 1.35/1.57      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.35/1.57         ((k4_zfmisc_1 @ X25 @ X26 @ X27 @ X28)
% 1.35/1.57           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X25 @ X26 @ X27) @ X28))),
% 1.35/1.57      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 1.35/1.57  thf('189', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         ((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0)
% 1.35/1.57           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 1.35/1.57      inference('sup+', [status(thm)], ['187', '188'])).
% 1.35/1.57  thf('190', plain,
% 1.35/1.57      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 1.35/1.57      inference('demod', [status(thm)], ['85', '87'])).
% 1.35/1.57  thf('191', plain,
% 1.35/1.57      (![X0 : $i]: ((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0) = (k1_xboole_0))),
% 1.35/1.57      inference('demod', [status(thm)], ['189', '190'])).
% 1.35/1.57  thf('192', plain,
% 1.35/1.57      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 1.35/1.57         (((k4_zfmisc_1 @ X43 @ X44 @ X45 @ X46) != (k1_xboole_0))
% 1.35/1.57          | ((X46) = (k1_xboole_0))
% 1.35/1.57          | ((X45) = (k1_xboole_0))
% 1.35/1.57          | ((X44) = (k1_xboole_0))
% 1.35/1.57          | ((X43) = (k1_xboole_0)))),
% 1.35/1.57      inference('cnf', [status(esa)], [t55_mcart_1])).
% 1.35/1.57  thf('193', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (((k1_xboole_0) != (k1_xboole_0))
% 1.35/1.57          | ((sk_A) = (k1_xboole_0))
% 1.35/1.57          | ((sk_B_2) = (k1_xboole_0))
% 1.35/1.57          | ((sk_C) = (k1_xboole_0))
% 1.35/1.57          | ((X0) = (k1_xboole_0)))),
% 1.35/1.57      inference('sup-', [status(thm)], ['191', '192'])).
% 1.35/1.57  thf('194', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (((X0) = (k1_xboole_0))
% 1.35/1.57          | ((sk_C) = (k1_xboole_0))
% 1.35/1.57          | ((sk_B_2) = (k1_xboole_0))
% 1.35/1.57          | ((sk_A) = (k1_xboole_0)))),
% 1.35/1.57      inference('simplify', [status(thm)], ['193'])).
% 1.35/1.57  thf('195', plain, (((sk_A) != (k1_xboole_0))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('196', plain, (((sk_B_2) != (k1_xboole_0))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('197', plain, (((sk_C) != (k1_xboole_0))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('198', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 1.35/1.57      inference('simplify_reflect-', [status(thm)],
% 1.35/1.57                ['194', '195', '196', '197'])).
% 1.35/1.57  thf('199', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 1.35/1.57      inference('demod', [status(thm)], ['0', '198'])).
% 1.35/1.57  thf('200', plain, ($false), inference('simplify', [status(thm)], ['199'])).
% 1.35/1.57  
% 1.35/1.57  % SZS output end Refutation
% 1.35/1.57  
% 1.35/1.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
