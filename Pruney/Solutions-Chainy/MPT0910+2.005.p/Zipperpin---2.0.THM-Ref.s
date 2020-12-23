%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.609y8Ge8GB

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 202 expanded)
%              Number of leaves         :   32 (  73 expanded)
%              Depth                    :   20
%              Number of atoms          : 1050 (3235 expanded)
%              Number of equality atoms :  101 ( 378 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_zfmisc_1 @ X17 @ X18 @ X19 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t24_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) )
             => ( C
                = ( k4_tarski @ ( k1_mcart_1 @ C ) @ ( k2_mcart_1 @ C ) ) ) ) ) )).

thf('2',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( X29 = k1_xboole_0 )
      | ( X30
        = ( k4_tarski @ ( k1_mcart_1 @ X30 ) @ ( k2_mcart_1 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k2_zfmisc_1 @ X29 @ X31 ) )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t24_mcart_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ( X3
        = ( k4_tarski @ ( k1_mcart_1 @ X3 ) @ ( k2_mcart_1 @ X3 ) ) )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf(fc1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( v1_xboole_0 @ ( k4_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v1_xboole_0 @ ( k4_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc1_zfmisc_1])).

thf('8',plain,
    ( ~ ( v1_xboole_0 @ sk_E )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ X8 )
      | ( r2_hidden @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('11',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t23_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( A
          = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ) )).

thf('12',plain,(
    ! [X27: $i,X28: $i] :
      ( ( X27
        = ( k4_tarski @ ( k1_mcart_1 @ X27 ) @ ( k2_mcart_1 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X28 )
      | ~ ( r2_hidden @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('13',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_zfmisc_1 @ X17 @ X18 @ X19 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('15',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( v1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X9 @ X8 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('20',plain,
    ( ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
    | ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('23',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_zfmisc_1 @ X17 @ X18 @ X19 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('24',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X24 ) @ X25 )
      | ~ ( r2_hidden @ X24 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X24 ) @ X25 )
      | ~ ( r2_hidden @ X24 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('28',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('30',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
    | ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('31',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('32',plain,
    ( ( v1_xboole_0 @ sk_E )
    | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('34',plain,(
    ! [X27: $i,X28: $i] :
      ( ( X27
        = ( k4_tarski @ ( k1_mcart_1 @ X27 ) @ ( k2_mcart_1 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X28 )
      | ~ ( r2_hidden @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('35',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('39',plain,
    ( ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
    | ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('40',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_mcart_1 @ X14 @ X15 @ X16 )
      = ( k4_tarski @ ( k4_tarski @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X0 )
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ sk_E ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('43',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X24 ) @ X26 )
      | ~ ( r2_hidden @ X24 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('46',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B )
    | ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('48',plain,
    ( ( v1_xboole_0 @ sk_E )
    | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X36 @ sk_B )
      | ( sk_D = X36 )
      | ( sk_E
       != ( k3_mcart_1 @ X37 @ X36 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ sk_C )
      | ~ ( m1_subset_1 @ X37 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_E )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_E
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 ) )
      | ( sk_D
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    sk_D
 != ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
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

thf('53',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( X32 = k1_xboole_0 )
      | ( X33 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X32 @ X33 @ X35 @ X34 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k3_zfmisc_1 @ X32 @ X33 @ X35 ) )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('54',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['54','55','56','57'])).

thf('59',plain,(
    sk_D
 != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['51','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_E )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_E
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['50','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ sk_E )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
      | ( v1_xboole_0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['41','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ( v1_xboole_0 @ sk_E )
      | ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_E )
      | ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ sk_E )
      | ~ ( m1_subset_1 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['32','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_C )
      | ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ sk_E ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( sk_E != sk_E )
    | ( v1_xboole_0 @ sk_E )
    | ( v1_xboole_0 @ sk_E )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['21','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ) )).

thf('67',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( m1_subset_1 @ ( k7_mcart_1 @ X20 @ X21 @ X22 @ X23 ) @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k3_zfmisc_1 @ X20 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_mcart_1])).

thf('68',plain,(
    m1_subset_1 @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_C ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( X32 = k1_xboole_0 )
      | ( X33 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X32 @ X33 @ X35 @ X34 )
        = ( k2_mcart_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k3_zfmisc_1 @ X32 @ X33 @ X35 ) )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('71',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k2_mcart_1 @ sk_E ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['71','72','73','74'])).

thf('76',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['68','75'])).

thf('77',plain,
    ( ( sk_E != sk_E )
    | ( v1_xboole_0 @ sk_E )
    | ( v1_xboole_0 @ sk_E ) ),
    inference(demod,[status(thm)],['65','76'])).

thf('78',plain,(
    v1_xboole_0 @ sk_E ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['8','78'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('80',plain,(
    ! [X2: $i,X3: $i] :
      ( ( X2 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('81',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['82','83','84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.609y8Ge8GB
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % DateTime   : Tue Dec  1 19:48:52 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 209 iterations in 0.093s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.55  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.55  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.20/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.55  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.55  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.55  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.55  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.20/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.55  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.55  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(t70_mcart_1, conjecture,
% 0.20/0.55    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.55       ( ( ![F:$i]:
% 0.20/0.55           ( ( m1_subset_1 @ F @ A ) =>
% 0.20/0.55             ( ![G:$i]:
% 0.20/0.55               ( ( m1_subset_1 @ G @ B ) =>
% 0.20/0.55                 ( ![H:$i]:
% 0.20/0.55                   ( ( m1_subset_1 @ H @ C ) =>
% 0.20/0.55                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.20/0.55                       ( ( D ) = ( G ) ) ) ) ) ) ) ) ) =>
% 0.20/0.55         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.55           ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.20/0.55           ( ( D ) = ( k6_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.55        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.55          ( ( ![F:$i]:
% 0.20/0.55              ( ( m1_subset_1 @ F @ A ) =>
% 0.20/0.55                ( ![G:$i]:
% 0.20/0.55                  ( ( m1_subset_1 @ G @ B ) =>
% 0.20/0.55                    ( ![H:$i]:
% 0.20/0.55                      ( ( m1_subset_1 @ H @ C ) =>
% 0.20/0.55                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.20/0.55                          ( ( D ) = ( G ) ) ) ) ) ) ) ) ) =>
% 0.20/0.55            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.55              ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.20/0.55              ( ( D ) = ( k6_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t70_mcart_1])).
% 0.20/0.55  thf('0', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(d3_zfmisc_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.20/0.55       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.20/0.55  thf('1', plain,
% 0.20/0.55      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.55         ((k3_zfmisc_1 @ X17 @ X18 @ X19)
% 0.20/0.55           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18) @ X19))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.55  thf(t24_mcart_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.55          ( ~( ![C:$i]:
% 0.20/0.55               ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 0.20/0.55                 ( ( C ) =
% 0.20/0.55                   ( k4_tarski @ ( k1_mcart_1 @ C ) @ ( k2_mcart_1 @ C ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf('2', plain,
% 0.20/0.55      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.20/0.55         (((X29) = (k1_xboole_0))
% 0.20/0.55          | ((X30) = (k4_tarski @ (k1_mcart_1 @ X30) @ (k2_mcart_1 @ X30)))
% 0.20/0.55          | ~ (m1_subset_1 @ X30 @ (k2_zfmisc_1 @ X29 @ X31))
% 0.20/0.55          | ((X31) = (k1_xboole_0)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t24_mcart_1])).
% 0.20/0.55  thf('3', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.20/0.55          | ((X0) = (k1_xboole_0))
% 0.20/0.55          | ((X3) = (k4_tarski @ (k1_mcart_1 @ X3) @ (k2_mcart_1 @ X3)))
% 0.20/0.55          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.55  thf('4', plain,
% 0.20/0.55      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.20/0.55        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.20/0.55        | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.55  thf('5', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('6', plain,
% 0.20/0.55      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.20/0.55        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.20/0.55      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.20/0.55  thf(fc1_zfmisc_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]: ( ~( v1_xboole_0 @ ( k4_tarski @ A @ B ) ) ))).
% 0.20/0.55  thf('7', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]: ~ (v1_xboole_0 @ (k4_tarski @ X0 @ X1))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc1_zfmisc_1])).
% 0.20/0.55  thf('8', plain,
% 0.20/0.55      ((~ (v1_xboole_0 @ sk_E) | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.55  thf('9', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(d2_subset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( v1_xboole_0 @ A ) =>
% 0.20/0.55         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.20/0.55       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.55         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.55  thf('10', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X7 @ X8)
% 0.20/0.55          | (r2_hidden @ X7 @ X8)
% 0.20/0.55          | (v1_xboole_0 @ X8))),
% 0.20/0.55      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.55  thf('11', plain,
% 0.20/0.55      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.20/0.55        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.55  thf(t23_mcart_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ B ) =>
% 0.20/0.55       ( ( r2_hidden @ A @ B ) =>
% 0.20/0.55         ( ( A ) = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ))).
% 0.20/0.55  thf('12', plain,
% 0.20/0.55      (![X27 : $i, X28 : $i]:
% 0.20/0.55         (((X27) = (k4_tarski @ (k1_mcart_1 @ X27) @ (k2_mcart_1 @ X27)))
% 0.20/0.55          | ~ (v1_relat_1 @ X28)
% 0.20/0.55          | ~ (r2_hidden @ X27 @ X28))),
% 0.20/0.55      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.20/0.55  thf('13', plain,
% 0.20/0.55      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.20/0.55        | ~ (v1_relat_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.20/0.55        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.55  thf('14', plain,
% 0.20/0.55      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.55         ((k3_zfmisc_1 @ X17 @ X18 @ X19)
% 0.20/0.55           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18) @ X19))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.55  thf(fc6_relat_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.55  thf('15', plain,
% 0.20/0.55      (![X12 : $i, X13 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X12 @ X13))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.55  thf('16', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         (v1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['14', '15'])).
% 0.20/0.55  thf('17', plain,
% 0.20/0.55      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.20/0.55        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.20/0.55      inference('demod', [status(thm)], ['13', '16'])).
% 0.20/0.55  thf('18', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('19', plain,
% 0.20/0.55      (![X8 : $i, X9 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X9 @ X8) | (v1_xboole_0 @ X9) | ~ (v1_xboole_0 @ X8))),
% 0.20/0.55      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.55  thf('20', plain,
% 0.20/0.55      ((~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.20/0.55        | (v1_xboole_0 @ sk_E))),
% 0.20/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.55  thf('21', plain,
% 0.20/0.55      ((((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.20/0.55        | (v1_xboole_0 @ sk_E))),
% 0.20/0.55      inference('sup-', [status(thm)], ['17', '20'])).
% 0.20/0.55  thf('22', plain,
% 0.20/0.55      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.20/0.55        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.55  thf('23', plain,
% 0.20/0.55      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.55         ((k3_zfmisc_1 @ X17 @ X18 @ X19)
% 0.20/0.55           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18) @ X19))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.55  thf(t10_mcart_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.20/0.55       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.55         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.20/0.55  thf('24', plain,
% 0.20/0.55      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.55         ((r2_hidden @ (k1_mcart_1 @ X24) @ X25)
% 0.20/0.55          | ~ (r2_hidden @ X24 @ (k2_zfmisc_1 @ X25 @ X26)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.55  thf('25', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.20/0.55          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.55  thf('26', plain,
% 0.20/0.55      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.20/0.55        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['22', '25'])).
% 0.20/0.55  thf('27', plain,
% 0.20/0.55      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.55         ((r2_hidden @ (k1_mcart_1 @ X24) @ X25)
% 0.20/0.55          | ~ (r2_hidden @ X24 @ (k2_zfmisc_1 @ X25 @ X26)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.55  thf('28', plain,
% 0.20/0.55      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.20/0.55        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.55  thf('29', plain,
% 0.20/0.55      ((~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.20/0.55        | (v1_xboole_0 @ sk_E))),
% 0.20/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.55  thf('30', plain,
% 0.20/0.55      (((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 0.20/0.55        | (v1_xboole_0 @ sk_E))),
% 0.20/0.55      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.55  thf(t1_subset, axiom,
% 0.20/0.55    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.20/0.55  thf('31', plain,
% 0.20/0.55      (![X10 : $i, X11 : $i]:
% 0.20/0.55         ((m1_subset_1 @ X10 @ X11) | ~ (r2_hidden @ X10 @ X11))),
% 0.20/0.55      inference('cnf', [status(esa)], [t1_subset])).
% 0.20/0.55  thf('32', plain,
% 0.20/0.55      (((v1_xboole_0 @ sk_E)
% 0.20/0.55        | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.55  thf('33', plain,
% 0.20/0.55      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.20/0.55        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['22', '25'])).
% 0.20/0.55  thf('34', plain,
% 0.20/0.55      (![X27 : $i, X28 : $i]:
% 0.20/0.55         (((X27) = (k4_tarski @ (k1_mcart_1 @ X27) @ (k2_mcart_1 @ X27)))
% 0.20/0.55          | ~ (v1_relat_1 @ X28)
% 0.20/0.55          | ~ (r2_hidden @ X27 @ X28))),
% 0.20/0.55      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.20/0.55  thf('35', plain,
% 0.20/0.55      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.20/0.55        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.20/0.55        | ((k1_mcart_1 @ sk_E)
% 0.20/0.55            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.20/0.55               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.55  thf('36', plain,
% 0.20/0.55      (![X12 : $i, X13 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X12 @ X13))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.55  thf('37', plain,
% 0.20/0.55      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.20/0.55        | ((k1_mcart_1 @ sk_E)
% 0.20/0.55            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.20/0.55               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 0.20/0.55      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.55  thf('38', plain,
% 0.20/0.55      ((~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.20/0.55        | (v1_xboole_0 @ sk_E))),
% 0.20/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.55  thf('39', plain,
% 0.20/0.55      ((((k1_mcart_1 @ sk_E)
% 0.20/0.55          = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.20/0.55             (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 0.20/0.55        | (v1_xboole_0 @ sk_E))),
% 0.20/0.55      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.55  thf(d3_mcart_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.20/0.55  thf('40', plain,
% 0.20/0.55      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.55         ((k3_mcart_1 @ X14 @ X15 @ X16)
% 0.20/0.55           = (k4_tarski @ (k4_tarski @ X14 @ X15) @ X16))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.20/0.55  thf('41', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.20/0.55            (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X0)
% 0.20/0.55            = (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.20/0.55          | (v1_xboole_0 @ sk_E))),
% 0.20/0.55      inference('sup+', [status(thm)], ['39', '40'])).
% 0.20/0.55  thf('42', plain,
% 0.20/0.55      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.20/0.55        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['22', '25'])).
% 0.20/0.55  thf('43', plain,
% 0.20/0.55      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.55         ((r2_hidden @ (k2_mcart_1 @ X24) @ X26)
% 0.20/0.55          | ~ (r2_hidden @ X24 @ (k2_zfmisc_1 @ X25 @ X26)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.55  thf('44', plain,
% 0.20/0.55      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.20/0.55        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.55  thf('45', plain,
% 0.20/0.55      ((~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.20/0.55        | (v1_xboole_0 @ sk_E))),
% 0.20/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.55  thf('46', plain,
% 0.20/0.55      (((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B)
% 0.20/0.55        | (v1_xboole_0 @ sk_E))),
% 0.20/0.55      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.55  thf('47', plain,
% 0.20/0.55      (![X10 : $i, X11 : $i]:
% 0.20/0.55         ((m1_subset_1 @ X10 @ X11) | ~ (r2_hidden @ X10 @ X11))),
% 0.20/0.55      inference('cnf', [status(esa)], [t1_subset])).
% 0.20/0.55  thf('48', plain,
% 0.20/0.55      (((v1_xboole_0 @ sk_E)
% 0.20/0.55        | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.55  thf('49', plain,
% 0.20/0.55      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X36 @ sk_B)
% 0.20/0.55          | ((sk_D) = (X36))
% 0.20/0.55          | ((sk_E) != (k3_mcart_1 @ X37 @ X36 @ X38))
% 0.20/0.55          | ~ (m1_subset_1 @ X38 @ sk_C)
% 0.20/0.55          | ~ (m1_subset_1 @ X37 @ sk_A))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('50', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((v1_xboole_0 @ sk_E)
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.55          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.20/0.55          | ((sk_E)
% 0.20/0.55              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1))
% 0.20/0.55          | ((sk_D) = (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.55  thf('51', plain, (((sk_D) != (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('52', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(t50_mcart_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.55          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.20/0.55          ( ~( ![D:$i]:
% 0.20/0.55               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.55                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.20/0.55                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.20/0.55                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.20/0.55                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.20/0.55                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf('53', plain,
% 0.20/0.55      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.20/0.55         (((X32) = (k1_xboole_0))
% 0.20/0.55          | ((X33) = (k1_xboole_0))
% 0.20/0.55          | ((k6_mcart_1 @ X32 @ X33 @ X35 @ X34)
% 0.20/0.55              = (k2_mcart_1 @ (k1_mcart_1 @ X34)))
% 0.20/0.55          | ~ (m1_subset_1 @ X34 @ (k3_zfmisc_1 @ X32 @ X33 @ X35))
% 0.20/0.55          | ((X35) = (k1_xboole_0)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.20/0.55  thf('54', plain,
% 0.20/0.55      ((((sk_C) = (k1_xboole_0))
% 0.20/0.55        | ((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.20/0.55            = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.20/0.55        | ((sk_B) = (k1_xboole_0))
% 0.20/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.55  thf('55', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('56', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('57', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('58', plain,
% 0.20/0.55      (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.20/0.55         = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 0.20/0.55      inference('simplify_reflect-', [status(thm)], ['54', '55', '56', '57'])).
% 0.20/0.55  thf('59', plain, (((sk_D) != (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 0.20/0.55      inference('demod', [status(thm)], ['51', '58'])).
% 0.20/0.55  thf('60', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((v1_xboole_0 @ sk_E)
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.55          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.20/0.55          | ((sk_E)
% 0.20/0.55              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1)))),
% 0.20/0.55      inference('simplify_reflect-', [status(thm)], ['50', '59'])).
% 0.20/0.55  thf('61', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.20/0.55          | (v1_xboole_0 @ sk_E)
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ sk_C)
% 0.20/0.55          | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 0.20/0.55          | (v1_xboole_0 @ sk_E))),
% 0.20/0.55      inference('sup-', [status(thm)], ['41', '60'])).
% 0.20/0.55  thf('62', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ sk_C)
% 0.20/0.55          | (v1_xboole_0 @ sk_E)
% 0.20/0.55          | ((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['61'])).
% 0.20/0.55  thf('63', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((v1_xboole_0 @ sk_E)
% 0.20/0.55          | ((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.20/0.55          | (v1_xboole_0 @ sk_E)
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ sk_C))),
% 0.20/0.55      inference('sup-', [status(thm)], ['32', '62'])).
% 0.20/0.55  thf('64', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X0 @ sk_C)
% 0.20/0.55          | ((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.20/0.55          | (v1_xboole_0 @ sk_E))),
% 0.20/0.55      inference('simplify', [status(thm)], ['63'])).
% 0.20/0.55  thf('65', plain,
% 0.20/0.55      ((((sk_E) != (sk_E))
% 0.20/0.55        | (v1_xboole_0 @ sk_E)
% 0.20/0.55        | (v1_xboole_0 @ sk_E)
% 0.20/0.55        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C))),
% 0.20/0.55      inference('sup-', [status(thm)], ['21', '64'])).
% 0.20/0.55  thf('66', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(dt_k7_mcart_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.55       ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ))).
% 0.20/0.55  thf('67', plain,
% 0.20/0.55      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.55         ((m1_subset_1 @ (k7_mcart_1 @ X20 @ X21 @ X22 @ X23) @ X22)
% 0.20/0.55          | ~ (m1_subset_1 @ X23 @ (k3_zfmisc_1 @ X20 @ X21 @ X22)))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_k7_mcart_1])).
% 0.20/0.55  thf('68', plain,
% 0.20/0.55      ((m1_subset_1 @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_C)),
% 0.20/0.55      inference('sup-', [status(thm)], ['66', '67'])).
% 0.20/0.55  thf('69', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('70', plain,
% 0.20/0.55      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.20/0.55         (((X32) = (k1_xboole_0))
% 0.20/0.55          | ((X33) = (k1_xboole_0))
% 0.20/0.55          | ((k7_mcart_1 @ X32 @ X33 @ X35 @ X34) = (k2_mcart_1 @ X34))
% 0.20/0.55          | ~ (m1_subset_1 @ X34 @ (k3_zfmisc_1 @ X32 @ X33 @ X35))
% 0.20/0.55          | ((X35) = (k1_xboole_0)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.20/0.55  thf('71', plain,
% 0.20/0.55      ((((sk_C) = (k1_xboole_0))
% 0.20/0.55        | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))
% 0.20/0.55        | ((sk_B) = (k1_xboole_0))
% 0.20/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['69', '70'])).
% 0.20/0.55  thf('72', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('73', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('74', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('75', plain,
% 0.20/0.55      (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))),
% 0.20/0.55      inference('simplify_reflect-', [status(thm)], ['71', '72', '73', '74'])).
% 0.20/0.55  thf('76', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)),
% 0.20/0.55      inference('demod', [status(thm)], ['68', '75'])).
% 0.20/0.55  thf('77', plain,
% 0.20/0.55      ((((sk_E) != (sk_E)) | (v1_xboole_0 @ sk_E) | (v1_xboole_0 @ sk_E))),
% 0.20/0.55      inference('demod', [status(thm)], ['65', '76'])).
% 0.20/0.55  thf('78', plain, ((v1_xboole_0 @ sk_E)),
% 0.20/0.55      inference('simplify', [status(thm)], ['77'])).
% 0.20/0.55  thf('79', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.55      inference('demod', [status(thm)], ['8', '78'])).
% 0.20/0.55  thf(t113_zfmisc_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.55       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.55  thf('80', plain,
% 0.20/0.55      (![X2 : $i, X3 : $i]:
% 0.20/0.55         (((X2) = (k1_xboole_0))
% 0.20/0.55          | ((X3) = (k1_xboole_0))
% 0.20/0.55          | ((k2_zfmisc_1 @ X3 @ X2) != (k1_xboole_0)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.55  thf('81', plain,
% 0.20/0.55      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.55        | ((sk_A) = (k1_xboole_0))
% 0.20/0.55        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['79', '80'])).
% 0.20/0.55  thf('82', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['81'])).
% 0.20/0.55  thf('83', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('84', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('85', plain, ($false),
% 0.20/0.55      inference('simplify_reflect-', [status(thm)], ['82', '83', '84'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
