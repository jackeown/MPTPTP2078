%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mjNaXvAIa5

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:59 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 563 expanded)
%              Number of leaves         :   37 ( 196 expanded)
%              Depth                    :   22
%              Number of atoms          : 1473 (7455 expanded)
%              Number of equality atoms :  191 (1107 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('0',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_zfmisc_1 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t195_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = A )
            & ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = B ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) )
        = X7 )
      | ( X7 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('2',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('3',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X6 = o_0_0_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) )
        = X7 )
      | ( X7 = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
        = X0 )
      | ( X0 = o_0_0_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = o_0_0_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

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

thf('6',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X2 )
      | ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t23_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( A
          = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ) )).

thf('9',plain,(
    ! [X29: $i,X30: $i] :
      ( ( X29
        = ( k4_tarski @ ( k1_mcart_1 @ X29 ) @ ( k2_mcart_1 @ X29 ) ) )
      | ~ ( v1_relat_1 @ X30 )
      | ~ ( r2_hidden @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('10',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_zfmisc_1 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('12',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( v1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf(fc11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X3: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X3 ) )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('17',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,
    ( ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
    | ( ( k2_relat_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,
    ( ( sk_C = o_0_0_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = o_0_0_xboole_0 )
    | ( sk_C = o_0_0_xboole_0 )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference('sup+',[status(thm)],['5','20'])).

thf('22',plain,
    ( ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = o_0_0_xboole_0 )
    | ( sk_C = o_0_0_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('25',plain,(
    sk_C != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = o_0_0_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['22','25'])).

thf('27',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('28',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_zfmisc_1 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('29',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X26 ) @ X27 )
      | ~ ( r2_hidden @ X26 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X29: $i,X30: $i] :
      ( ( X29
        = ( k4_tarski @ ( k1_mcart_1 @ X29 ) @ ( k2_mcart_1 @ X29 ) ) )
      | ~ ( v1_relat_1 @ X30 )
      | ~ ( r2_hidden @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('35',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('36',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_mcart_1 @ X8 @ X9 @ X10 )
      = ( k4_tarski @ ( k4_tarski @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X0 )
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k6_mcart_1 @ A @ B @ C @ D ) @ B ) ) )).

thf('39',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( m1_subset_1 @ ( k6_mcart_1 @ X18 @ X19 @ X20 @ X21 ) @ X19 )
      | ~ ( m1_subset_1 @ X21 @ ( k3_zfmisc_1 @ X18 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_mcart_1])).

thf('40',plain,(
    m1_subset_1 @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_B ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
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

thf('42',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( X31 = k1_xboole_0 )
      | ( X32 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X31 @ X32 @ X34 @ X33 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k3_zfmisc_1 @ X31 @ X32 @ X34 ) )
      | ( X34 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('43',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('44',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('45',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('46',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( X31 = o_0_0_xboole_0 )
      | ( X32 = o_0_0_xboole_0 )
      | ( ( k6_mcart_1 @ X31 @ X32 @ X34 @ X33 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k3_zfmisc_1 @ X31 @ X32 @ X34 ) )
      | ( X34 = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('47',plain,
    ( ( sk_C = o_0_0_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    | ( sk_B = o_0_0_xboole_0 )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('50',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('53',plain,(
    sk_B != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    sk_C != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['23','24'])).

thf('55',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['47','50','53','54'])).

thf('56',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B ),
    inference(demod,[status(thm)],['40','55'])).

thf('57',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ sk_B )
      | ( sk_E
       != ( k3_mcart_1 @ X36 @ X35 @ X37 ) )
      | ( sk_D = X37 )
      | ~ ( m1_subset_1 @ X37 @ sk_C )
      | ~ ( m1_subset_1 @ X36 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_D = X1 )
      | ( sk_E
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ A ) ) )).

thf('61',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k5_mcart_1 @ X14 @ X15 @ X16 @ X17 ) @ X14 )
      | ~ ( m1_subset_1 @ X17 @ ( k3_zfmisc_1 @ X14 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_mcart_1])).

thf('62',plain,(
    m1_subset_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_A ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( X31 = k1_xboole_0 )
      | ( X32 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X31 @ X32 @ X34 @ X33 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k3_zfmisc_1 @ X31 @ X32 @ X34 ) )
      | ( X34 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('65',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('66',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('67',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('68',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( X31 = o_0_0_xboole_0 )
      | ( X32 = o_0_0_xboole_0 )
      | ( ( k5_mcart_1 @ X31 @ X32 @ X34 @ X33 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k3_zfmisc_1 @ X31 @ X32 @ X34 ) )
      | ( X34 = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['64','65','66','67'])).

thf('69',plain,
    ( ( sk_C = o_0_0_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    | ( sk_B = o_0_0_xboole_0 )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','68'])).

thf('70',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['48','49'])).

thf('71',plain,(
    sk_B != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['51','52'])).

thf('72',plain,(
    sk_C != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['23','24'])).

thf('73',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['69','70','71','72'])).

thf('74',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ),
    inference(demod,[status(thm)],['62','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['59','74'])).

thf('76',plain,
    ( ( sk_E != sk_E )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = o_0_0_xboole_0 )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) )
    | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ) )).

thf('78',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( m1_subset_1 @ ( k7_mcart_1 @ X22 @ X23 @ X24 @ X25 ) @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k3_zfmisc_1 @ X22 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_mcart_1])).

thf('79',plain,(
    m1_subset_1 @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_C ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( X31 = k1_xboole_0 )
      | ( X32 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X31 @ X32 @ X34 @ X33 )
        = ( k2_mcart_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k3_zfmisc_1 @ X31 @ X32 @ X34 ) )
      | ( X34 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('82',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('83',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('84',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('85',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( X31 = o_0_0_xboole_0 )
      | ( X32 = o_0_0_xboole_0 )
      | ( ( k7_mcart_1 @ X31 @ X32 @ X34 @ X33 )
        = ( k2_mcart_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k3_zfmisc_1 @ X31 @ X32 @ X34 ) )
      | ( X34 = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('86',plain,
    ( ( sk_C = o_0_0_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k2_mcart_1 @ sk_E ) )
    | ( sk_B = o_0_0_xboole_0 )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','85'])).

thf('87',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['48','49'])).

thf('88',plain,(
    sk_B != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['51','52'])).

thf('89',plain,(
    sk_C != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['23','24'])).

thf('90',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['86','87','88','89'])).

thf('91',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['79','90'])).

thf('92',plain,
    ( ( sk_E != sk_E )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = o_0_0_xboole_0 )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) )
    | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['76','91'])).

thf('93',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = o_0_0_xboole_0 ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    sk_D
 != ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['86','87','88','89'])).

thf('96',plain,(
    sk_D
 != ( k2_mcart_1 @ sk_E ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = o_0_0_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['93','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
        = X0 )
      | ( X0 = o_0_0_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = o_0_0_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf('99',plain,(
    ! [X3: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X3 ) )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = o_0_0_xboole_0 )
      | ( X0 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = o_0_0_xboole_0 )
    | ( sk_C = o_0_0_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = o_0_0_xboole_0 )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['97','100'])).

thf('102',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( sk_C = o_0_0_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = o_0_0_xboole_0 ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    sk_C != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['23','24'])).

thf('104',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = o_0_0_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X6 = o_0_0_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) )
        = X7 )
      | ( X7 = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf('106',plain,
    ( ( ( k2_relat_1 @ o_0_0_xboole_0 )
      = sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( sk_B = o_0_0_xboole_0 )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('108',plain,(
    ! [X3: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X3 ) )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf('109',plain,(
    ! [X3: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X3 ) )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf('110',plain,(
    ! [X3: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X3 ) )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_relat_1 @ ( k2_relat_1 @ X0 ) )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_relat_1 @ ( k2_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['109','112'])).

thf('114',plain,(
    ! [X3: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X3 ) )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['108','115'])).

thf('117',plain,(
    ! [X3: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X3 ) )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
    | ( v1_xboole_0 @ o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['107','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['59','74'])).

thf('121',plain,
    ( ( sk_E != sk_E )
    | ( v1_xboole_0 @ o_0_0_xboole_0 )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) )
    | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['79','90'])).

thf('123',plain,
    ( ( sk_E != sk_E )
    | ( v1_xboole_0 @ o_0_0_xboole_0 )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) )
    | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) )
    | ( v1_xboole_0 @ o_0_0_xboole_0 ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    sk_D
 != ( k2_mcart_1 @ sk_E ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('126',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v1_xboole_0 @ o_0_0_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('128',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(clc,[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('130',plain,
    ( ( k2_relat_1 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( o_0_0_xboole_0 = sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( sk_B = o_0_0_xboole_0 )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['106','130'])).

thf('132',plain,
    ( ( sk_A = o_0_0_xboole_0 )
    | ( v1_xboole_0 @ sk_C )
    | ( o_0_0_xboole_0 = sk_B ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    sk_B != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['51','52'])).

thf('134',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['48','49'])).

thf('135',plain,(
    v1_xboole_0 @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['132','133','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('137',plain,(
    sk_C = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    sk_C != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['23','24'])).

thf('139',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['137','138'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mjNaXvAIa5
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:25:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.39/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.57  % Solved by: fo/fo7.sh
% 0.39/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.57  % done 365 iterations in 0.116s
% 0.39/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.57  % SZS output start Refutation
% 0.39/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.57  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.39/0.57  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.39/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.57  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.39/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.57  thf(sk_D_type, type, sk_D: $i).
% 0.39/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.57  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.39/0.57  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.39/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.57  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.39/0.57  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.39/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.57  thf(sk_E_type, type, sk_E: $i).
% 0.39/0.57  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.39/0.57  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.39/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.57  thf(d3_zfmisc_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.39/0.57       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.39/0.57  thf('0', plain,
% 0.39/0.57      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.39/0.57         ((k3_zfmisc_1 @ X11 @ X12 @ X13)
% 0.39/0.57           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12) @ X13))),
% 0.39/0.57      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.39/0.57  thf(t195_relat_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.39/0.57          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 0.39/0.57               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 0.39/0.57  thf('1', plain,
% 0.39/0.57      (![X6 : $i, X7 : $i]:
% 0.39/0.57         (((X6) = (k1_xboole_0))
% 0.39/0.57          | ((k2_relat_1 @ (k2_zfmisc_1 @ X6 @ X7)) = (X7))
% 0.39/0.57          | ((X7) = (k1_xboole_0)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.39/0.57  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.39/0.57  thf('2', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.39/0.57      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.39/0.57  thf('3', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.39/0.57      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.39/0.57  thf('4', plain,
% 0.39/0.57      (![X6 : $i, X7 : $i]:
% 0.39/0.57         (((X6) = (o_0_0_xboole_0))
% 0.39/0.57          | ((k2_relat_1 @ (k2_zfmisc_1 @ X6 @ X7)) = (X7))
% 0.39/0.57          | ((X7) = (o_0_0_xboole_0)))),
% 0.39/0.57      inference('demod', [status(thm)], ['1', '2', '3'])).
% 0.39/0.57  thf('5', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         (((k2_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0)) = (X0))
% 0.39/0.57          | ((X0) = (o_0_0_xboole_0))
% 0.39/0.57          | ((k2_zfmisc_1 @ X2 @ X1) = (o_0_0_xboole_0)))),
% 0.39/0.57      inference('sup+', [status(thm)], ['0', '4'])).
% 0.39/0.57  thf(t71_mcart_1, conjecture,
% 0.39/0.57    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.39/0.57       ( ( ![F:$i]:
% 0.39/0.57           ( ( m1_subset_1 @ F @ A ) =>
% 0.39/0.57             ( ![G:$i]:
% 0.39/0.57               ( ( m1_subset_1 @ G @ B ) =>
% 0.39/0.57                 ( ![H:$i]:
% 0.39/0.57                   ( ( m1_subset_1 @ H @ C ) =>
% 0.39/0.57                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.39/0.57                       ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 0.39/0.57         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.39/0.57           ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.39/0.57           ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 0.39/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.57    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.39/0.57        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.39/0.57          ( ( ![F:$i]:
% 0.39/0.57              ( ( m1_subset_1 @ F @ A ) =>
% 0.39/0.57                ( ![G:$i]:
% 0.39/0.57                  ( ( m1_subset_1 @ G @ B ) =>
% 0.39/0.57                    ( ![H:$i]:
% 0.39/0.57                      ( ( m1_subset_1 @ H @ C ) =>
% 0.39/0.57                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.39/0.57                          ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 0.39/0.57            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.39/0.57              ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.39/0.57              ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 0.39/0.57    inference('cnf.neg', [status(esa)], [t71_mcart_1])).
% 0.39/0.57  thf('6', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(t2_subset, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ A @ B ) =>
% 0.39/0.57       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.39/0.57  thf('7', plain,
% 0.39/0.57      (![X1 : $i, X2 : $i]:
% 0.39/0.57         ((r2_hidden @ X1 @ X2)
% 0.39/0.57          | (v1_xboole_0 @ X2)
% 0.39/0.57          | ~ (m1_subset_1 @ X1 @ X2))),
% 0.39/0.57      inference('cnf', [status(esa)], [t2_subset])).
% 0.39/0.57  thf('8', plain,
% 0.39/0.57      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.39/0.57        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.57  thf(t23_mcart_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ B ) =>
% 0.39/0.57       ( ( r2_hidden @ A @ B ) =>
% 0.39/0.57         ( ( A ) = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ))).
% 0.39/0.57  thf('9', plain,
% 0.39/0.57      (![X29 : $i, X30 : $i]:
% 0.39/0.57         (((X29) = (k4_tarski @ (k1_mcart_1 @ X29) @ (k2_mcart_1 @ X29)))
% 0.39/0.57          | ~ (v1_relat_1 @ X30)
% 0.39/0.57          | ~ (r2_hidden @ X29 @ X30))),
% 0.39/0.57      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.39/0.57  thf('10', plain,
% 0.39/0.57      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.39/0.57        | ~ (v1_relat_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.39/0.57        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['8', '9'])).
% 0.39/0.57  thf('11', plain,
% 0.39/0.57      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.39/0.57         ((k3_zfmisc_1 @ X11 @ X12 @ X13)
% 0.39/0.57           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12) @ X13))),
% 0.39/0.57      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.39/0.57  thf(fc6_relat_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.39/0.57  thf('12', plain,
% 0.39/0.57      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.39/0.57      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.39/0.57  thf('13', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         (v1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))),
% 0.39/0.57      inference('sup+', [status(thm)], ['11', '12'])).
% 0.39/0.57  thf('14', plain,
% 0.39/0.57      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.39/0.57        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.39/0.57      inference('demod', [status(thm)], ['10', '13'])).
% 0.39/0.57  thf(fc11_relat_1, axiom,
% 0.39/0.57    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ))).
% 0.39/0.57  thf('15', plain,
% 0.39/0.57      (![X3 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X3)) | ~ (v1_xboole_0 @ X3))),
% 0.39/0.57      inference('cnf', [status(esa)], [fc11_relat_1])).
% 0.39/0.57  thf(l13_xboole_0, axiom,
% 0.39/0.57    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.39/0.57  thf('16', plain,
% 0.39/0.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.39/0.57      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.39/0.57  thf('17', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.39/0.57      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.39/0.57  thf('18', plain,
% 0.39/0.57      (![X0 : $i]: (((X0) = (o_0_0_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.39/0.57      inference('demod', [status(thm)], ['16', '17'])).
% 0.39/0.57  thf('19', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (~ (v1_xboole_0 @ X0) | ((k2_relat_1 @ X0) = (o_0_0_xboole_0)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['15', '18'])).
% 0.39/0.57  thf('20', plain,
% 0.39/0.57      ((((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.39/0.57        | ((k2_relat_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)) = (o_0_0_xboole_0)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['14', '19'])).
% 0.39/0.57  thf('21', plain,
% 0.39/0.57      ((((sk_C) = (o_0_0_xboole_0))
% 0.39/0.57        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (o_0_0_xboole_0))
% 0.39/0.57        | ((sk_C) = (o_0_0_xboole_0))
% 0.39/0.57        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.39/0.57      inference('sup+', [status(thm)], ['5', '20'])).
% 0.39/0.57  thf('22', plain,
% 0.39/0.57      ((((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.39/0.57        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (o_0_0_xboole_0))
% 0.39/0.57        | ((sk_C) = (o_0_0_xboole_0)))),
% 0.39/0.57      inference('simplify', [status(thm)], ['21'])).
% 0.39/0.57  thf('23', plain, (((sk_C) != (k1_xboole_0))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('24', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.39/0.57      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.39/0.57  thf('25', plain, (((sk_C) != (o_0_0_xboole_0))),
% 0.39/0.57      inference('demod', [status(thm)], ['23', '24'])).
% 0.39/0.57  thf('26', plain,
% 0.39/0.57      ((((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.39/0.57        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (o_0_0_xboole_0)))),
% 0.39/0.57      inference('simplify_reflect-', [status(thm)], ['22', '25'])).
% 0.39/0.57  thf('27', plain,
% 0.39/0.57      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.39/0.57        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.57  thf('28', plain,
% 0.39/0.57      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.39/0.57         ((k3_zfmisc_1 @ X11 @ X12 @ X13)
% 0.39/0.57           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12) @ X13))),
% 0.39/0.57      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.39/0.57  thf(t10_mcart_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.39/0.57       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.39/0.57         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.39/0.57  thf('29', plain,
% 0.39/0.57      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.39/0.57         ((r2_hidden @ (k1_mcart_1 @ X26) @ X27)
% 0.39/0.57          | ~ (r2_hidden @ X26 @ (k2_zfmisc_1 @ X27 @ X28)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.39/0.57  thf('30', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.39/0.57          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['28', '29'])).
% 0.39/0.57  thf('31', plain,
% 0.39/0.57      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.39/0.57        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['27', '30'])).
% 0.39/0.57  thf('32', plain,
% 0.39/0.57      (![X29 : $i, X30 : $i]:
% 0.39/0.57         (((X29) = (k4_tarski @ (k1_mcart_1 @ X29) @ (k2_mcart_1 @ X29)))
% 0.39/0.57          | ~ (v1_relat_1 @ X30)
% 0.39/0.57          | ~ (r2_hidden @ X29 @ X30))),
% 0.39/0.57      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.39/0.57  thf('33', plain,
% 0.39/0.57      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.39/0.57        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.39/0.57        | ((k1_mcart_1 @ sk_E)
% 0.39/0.57            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.39/0.57               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['31', '32'])).
% 0.39/0.57  thf('34', plain,
% 0.39/0.57      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.39/0.57      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.39/0.57  thf('35', plain,
% 0.39/0.57      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.39/0.57        | ((k1_mcart_1 @ sk_E)
% 0.39/0.57            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.39/0.57               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 0.39/0.57      inference('demod', [status(thm)], ['33', '34'])).
% 0.39/0.57  thf(d3_mcart_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.39/0.57  thf('36', plain,
% 0.39/0.57      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.39/0.57         ((k3_mcart_1 @ X8 @ X9 @ X10)
% 0.39/0.57           = (k4_tarski @ (k4_tarski @ X8 @ X9) @ X10))),
% 0.39/0.57      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.39/0.57  thf('37', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.39/0.57            (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X0)
% 0.39/0.57            = (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.39/0.57          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 0.39/0.57      inference('sup+', [status(thm)], ['35', '36'])).
% 0.39/0.57  thf('38', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(dt_k6_mcart_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.39/0.57       ( m1_subset_1 @ ( k6_mcart_1 @ A @ B @ C @ D ) @ B ) ))).
% 0.39/0.57  thf('39', plain,
% 0.39/0.57      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.39/0.57         ((m1_subset_1 @ (k6_mcart_1 @ X18 @ X19 @ X20 @ X21) @ X19)
% 0.39/0.57          | ~ (m1_subset_1 @ X21 @ (k3_zfmisc_1 @ X18 @ X19 @ X20)))),
% 0.39/0.57      inference('cnf', [status(esa)], [dt_k6_mcart_1])).
% 0.39/0.57  thf('40', plain,
% 0.39/0.57      ((m1_subset_1 @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_B)),
% 0.39/0.57      inference('sup-', [status(thm)], ['38', '39'])).
% 0.39/0.57  thf('41', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(t50_mcart_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.39/0.57          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.39/0.57          ( ~( ![D:$i]:
% 0.39/0.57               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.39/0.57                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.39/0.57                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.39/0.57                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.39/0.57                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.39/0.57                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.39/0.57  thf('42', plain,
% 0.39/0.57      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.39/0.57         (((X31) = (k1_xboole_0))
% 0.39/0.57          | ((X32) = (k1_xboole_0))
% 0.39/0.57          | ((k6_mcart_1 @ X31 @ X32 @ X34 @ X33)
% 0.39/0.57              = (k2_mcart_1 @ (k1_mcart_1 @ X33)))
% 0.39/0.57          | ~ (m1_subset_1 @ X33 @ (k3_zfmisc_1 @ X31 @ X32 @ X34))
% 0.39/0.57          | ((X34) = (k1_xboole_0)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.39/0.57  thf('43', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.39/0.57      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.39/0.57  thf('44', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.39/0.57      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.39/0.57  thf('45', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.39/0.57      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.39/0.57  thf('46', plain,
% 0.39/0.57      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.39/0.57         (((X31) = (o_0_0_xboole_0))
% 0.39/0.57          | ((X32) = (o_0_0_xboole_0))
% 0.39/0.57          | ((k6_mcart_1 @ X31 @ X32 @ X34 @ X33)
% 0.39/0.57              = (k2_mcart_1 @ (k1_mcart_1 @ X33)))
% 0.39/0.57          | ~ (m1_subset_1 @ X33 @ (k3_zfmisc_1 @ X31 @ X32 @ X34))
% 0.39/0.57          | ((X34) = (o_0_0_xboole_0)))),
% 0.39/0.57      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 0.39/0.57  thf('47', plain,
% 0.39/0.57      ((((sk_C) = (o_0_0_xboole_0))
% 0.39/0.57        | ((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.39/0.57            = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.39/0.57        | ((sk_B) = (o_0_0_xboole_0))
% 0.39/0.57        | ((sk_A) = (o_0_0_xboole_0)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['41', '46'])).
% 0.39/0.57  thf('48', plain, (((sk_A) != (k1_xboole_0))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('49', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.39/0.57      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.39/0.57  thf('50', plain, (((sk_A) != (o_0_0_xboole_0))),
% 0.39/0.57      inference('demod', [status(thm)], ['48', '49'])).
% 0.39/0.57  thf('51', plain, (((sk_B) != (k1_xboole_0))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('52', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.39/0.57      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.39/0.57  thf('53', plain, (((sk_B) != (o_0_0_xboole_0))),
% 0.39/0.57      inference('demod', [status(thm)], ['51', '52'])).
% 0.39/0.57  thf('54', plain, (((sk_C) != (o_0_0_xboole_0))),
% 0.39/0.57      inference('demod', [status(thm)], ['23', '24'])).
% 0.39/0.57  thf('55', plain,
% 0.39/0.57      (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.39/0.57         = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 0.39/0.57      inference('simplify_reflect-', [status(thm)], ['47', '50', '53', '54'])).
% 0.39/0.57  thf('56', plain, ((m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B)),
% 0.39/0.57      inference('demod', [status(thm)], ['40', '55'])).
% 0.39/0.57  thf('57', plain,
% 0.39/0.57      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X35 @ sk_B)
% 0.39/0.57          | ((sk_E) != (k3_mcart_1 @ X36 @ X35 @ X37))
% 0.39/0.57          | ((sk_D) = (X37))
% 0.39/0.57          | ~ (m1_subset_1 @ X37 @ sk_C)
% 0.39/0.57          | ~ (m1_subset_1 @ X36 @ sk_A))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('58', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.39/0.57          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.39/0.57          | ((sk_D) = (X1))
% 0.39/0.57          | ((sk_E)
% 0.39/0.57              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['56', '57'])).
% 0.39/0.57  thf('59', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.39/0.57          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.39/0.57          | ((sk_D) = (X0))
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ sk_C)
% 0.39/0.57          | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['37', '58'])).
% 0.39/0.57  thf('60', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(dt_k5_mcart_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.39/0.57       ( m1_subset_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ A ) ))).
% 0.39/0.57  thf('61', plain,
% 0.39/0.57      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.39/0.57         ((m1_subset_1 @ (k5_mcart_1 @ X14 @ X15 @ X16 @ X17) @ X14)
% 0.39/0.57          | ~ (m1_subset_1 @ X17 @ (k3_zfmisc_1 @ X14 @ X15 @ X16)))),
% 0.39/0.57      inference('cnf', [status(esa)], [dt_k5_mcart_1])).
% 0.39/0.57  thf('62', plain,
% 0.39/0.57      ((m1_subset_1 @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_A)),
% 0.39/0.57      inference('sup-', [status(thm)], ['60', '61'])).
% 0.39/0.57  thf('63', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('64', plain,
% 0.39/0.57      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.39/0.57         (((X31) = (k1_xboole_0))
% 0.39/0.57          | ((X32) = (k1_xboole_0))
% 0.39/0.57          | ((k5_mcart_1 @ X31 @ X32 @ X34 @ X33)
% 0.39/0.57              = (k1_mcart_1 @ (k1_mcart_1 @ X33)))
% 0.39/0.57          | ~ (m1_subset_1 @ X33 @ (k3_zfmisc_1 @ X31 @ X32 @ X34))
% 0.39/0.57          | ((X34) = (k1_xboole_0)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.39/0.57  thf('65', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.39/0.57      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.39/0.57  thf('66', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.39/0.57      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.39/0.57  thf('67', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.39/0.57      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.39/0.57  thf('68', plain,
% 0.39/0.57      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.39/0.57         (((X31) = (o_0_0_xboole_0))
% 0.39/0.57          | ((X32) = (o_0_0_xboole_0))
% 0.39/0.57          | ((k5_mcart_1 @ X31 @ X32 @ X34 @ X33)
% 0.39/0.57              = (k1_mcart_1 @ (k1_mcart_1 @ X33)))
% 0.39/0.57          | ~ (m1_subset_1 @ X33 @ (k3_zfmisc_1 @ X31 @ X32 @ X34))
% 0.39/0.57          | ((X34) = (o_0_0_xboole_0)))),
% 0.39/0.57      inference('demod', [status(thm)], ['64', '65', '66', '67'])).
% 0.39/0.57  thf('69', plain,
% 0.39/0.57      ((((sk_C) = (o_0_0_xboole_0))
% 0.39/0.57        | ((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.39/0.57            = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.39/0.57        | ((sk_B) = (o_0_0_xboole_0))
% 0.39/0.57        | ((sk_A) = (o_0_0_xboole_0)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['63', '68'])).
% 0.39/0.57  thf('70', plain, (((sk_A) != (o_0_0_xboole_0))),
% 0.39/0.57      inference('demod', [status(thm)], ['48', '49'])).
% 0.39/0.57  thf('71', plain, (((sk_B) != (o_0_0_xboole_0))),
% 0.39/0.57      inference('demod', [status(thm)], ['51', '52'])).
% 0.39/0.57  thf('72', plain, (((sk_C) != (o_0_0_xboole_0))),
% 0.39/0.57      inference('demod', [status(thm)], ['23', '24'])).
% 0.39/0.57  thf('73', plain,
% 0.39/0.57      (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.39/0.57         = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 0.39/0.57      inference('simplify_reflect-', [status(thm)], ['69', '70', '71', '72'])).
% 0.39/0.57  thf('74', plain, ((m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)),
% 0.39/0.57      inference('demod', [status(thm)], ['62', '73'])).
% 0.39/0.57  thf('75', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.39/0.57          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.39/0.57          | ((sk_D) = (X0))
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ sk_C))),
% 0.39/0.57      inference('demod', [status(thm)], ['59', '74'])).
% 0.39/0.57  thf('76', plain,
% 0.39/0.57      ((((sk_E) != (sk_E))
% 0.39/0.57        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (o_0_0_xboole_0))
% 0.39/0.57        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)
% 0.39/0.57        | ((sk_D) = (k2_mcart_1 @ sk_E))
% 0.39/0.57        | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['26', '75'])).
% 0.39/0.57  thf('77', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(dt_k7_mcart_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.39/0.57       ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ))).
% 0.39/0.57  thf('78', plain,
% 0.39/0.57      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.39/0.57         ((m1_subset_1 @ (k7_mcart_1 @ X22 @ X23 @ X24 @ X25) @ X24)
% 0.39/0.57          | ~ (m1_subset_1 @ X25 @ (k3_zfmisc_1 @ X22 @ X23 @ X24)))),
% 0.39/0.57      inference('cnf', [status(esa)], [dt_k7_mcart_1])).
% 0.39/0.57  thf('79', plain,
% 0.39/0.57      ((m1_subset_1 @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_C)),
% 0.39/0.57      inference('sup-', [status(thm)], ['77', '78'])).
% 0.39/0.57  thf('80', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('81', plain,
% 0.39/0.57      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.39/0.57         (((X31) = (k1_xboole_0))
% 0.39/0.57          | ((X32) = (k1_xboole_0))
% 0.39/0.57          | ((k7_mcart_1 @ X31 @ X32 @ X34 @ X33) = (k2_mcart_1 @ X33))
% 0.39/0.57          | ~ (m1_subset_1 @ X33 @ (k3_zfmisc_1 @ X31 @ X32 @ X34))
% 0.39/0.57          | ((X34) = (k1_xboole_0)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.39/0.57  thf('82', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.39/0.57      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.39/0.57  thf('83', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.39/0.57      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.39/0.57  thf('84', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.39/0.57      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.39/0.57  thf('85', plain,
% 0.39/0.57      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.39/0.57         (((X31) = (o_0_0_xboole_0))
% 0.39/0.57          | ((X32) = (o_0_0_xboole_0))
% 0.39/0.57          | ((k7_mcart_1 @ X31 @ X32 @ X34 @ X33) = (k2_mcart_1 @ X33))
% 0.39/0.57          | ~ (m1_subset_1 @ X33 @ (k3_zfmisc_1 @ X31 @ X32 @ X34))
% 0.39/0.57          | ((X34) = (o_0_0_xboole_0)))),
% 0.39/0.57      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 0.39/0.57  thf('86', plain,
% 0.39/0.57      ((((sk_C) = (o_0_0_xboole_0))
% 0.39/0.57        | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))
% 0.39/0.57        | ((sk_B) = (o_0_0_xboole_0))
% 0.39/0.57        | ((sk_A) = (o_0_0_xboole_0)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['80', '85'])).
% 0.39/0.57  thf('87', plain, (((sk_A) != (o_0_0_xboole_0))),
% 0.39/0.57      inference('demod', [status(thm)], ['48', '49'])).
% 0.39/0.57  thf('88', plain, (((sk_B) != (o_0_0_xboole_0))),
% 0.39/0.57      inference('demod', [status(thm)], ['51', '52'])).
% 0.39/0.57  thf('89', plain, (((sk_C) != (o_0_0_xboole_0))),
% 0.39/0.57      inference('demod', [status(thm)], ['23', '24'])).
% 0.39/0.57  thf('90', plain,
% 0.39/0.57      (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))),
% 0.39/0.57      inference('simplify_reflect-', [status(thm)], ['86', '87', '88', '89'])).
% 0.39/0.57  thf('91', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)),
% 0.39/0.57      inference('demod', [status(thm)], ['79', '90'])).
% 0.39/0.57  thf('92', plain,
% 0.39/0.57      ((((sk_E) != (sk_E))
% 0.39/0.57        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (o_0_0_xboole_0))
% 0.39/0.57        | ((sk_D) = (k2_mcart_1 @ sk_E))
% 0.39/0.57        | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 0.39/0.57      inference('demod', [status(thm)], ['76', '91'])).
% 0.39/0.57  thf('93', plain,
% 0.39/0.57      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.39/0.57        | ((sk_D) = (k2_mcart_1 @ sk_E))
% 0.39/0.57        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (o_0_0_xboole_0)))),
% 0.39/0.57      inference('simplify', [status(thm)], ['92'])).
% 0.39/0.57  thf('94', plain, (((sk_D) != (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('95', plain,
% 0.39/0.57      (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))),
% 0.39/0.57      inference('simplify_reflect-', [status(thm)], ['86', '87', '88', '89'])).
% 0.39/0.57  thf('96', plain, (((sk_D) != (k2_mcart_1 @ sk_E))),
% 0.39/0.57      inference('demod', [status(thm)], ['94', '95'])).
% 0.39/0.57  thf('97', plain,
% 0.39/0.57      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.39/0.57        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (o_0_0_xboole_0)))),
% 0.39/0.57      inference('simplify_reflect-', [status(thm)], ['93', '96'])).
% 0.39/0.57  thf('98', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         (((k2_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0)) = (X0))
% 0.39/0.57          | ((X0) = (o_0_0_xboole_0))
% 0.39/0.57          | ((k2_zfmisc_1 @ X2 @ X1) = (o_0_0_xboole_0)))),
% 0.39/0.57      inference('sup+', [status(thm)], ['0', '4'])).
% 0.39/0.57  thf('99', plain,
% 0.39/0.57      (![X3 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X3)) | ~ (v1_xboole_0 @ X3))),
% 0.39/0.57      inference('cnf', [status(esa)], [fc11_relat_1])).
% 0.39/0.57  thf('100', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         ((v1_xboole_0 @ X0)
% 0.39/0.57          | ((k2_zfmisc_1 @ X2 @ X1) = (o_0_0_xboole_0))
% 0.39/0.57          | ((X0) = (o_0_0_xboole_0))
% 0.39/0.57          | ~ (v1_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0)))),
% 0.39/0.57      inference('sup+', [status(thm)], ['98', '99'])).
% 0.39/0.57  thf('101', plain,
% 0.39/0.57      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (o_0_0_xboole_0))
% 0.39/0.57        | ((sk_C) = (o_0_0_xboole_0))
% 0.39/0.57        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (o_0_0_xboole_0))
% 0.39/0.57        | (v1_xboole_0 @ sk_C))),
% 0.39/0.57      inference('sup-', [status(thm)], ['97', '100'])).
% 0.39/0.57  thf('102', plain,
% 0.39/0.57      (((v1_xboole_0 @ sk_C)
% 0.39/0.57        | ((sk_C) = (o_0_0_xboole_0))
% 0.39/0.57        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (o_0_0_xboole_0)))),
% 0.39/0.57      inference('simplify', [status(thm)], ['101'])).
% 0.39/0.57  thf('103', plain, (((sk_C) != (o_0_0_xboole_0))),
% 0.39/0.57      inference('demod', [status(thm)], ['23', '24'])).
% 0.39/0.57  thf('104', plain,
% 0.39/0.57      (((v1_xboole_0 @ sk_C) | ((k2_zfmisc_1 @ sk_A @ sk_B) = (o_0_0_xboole_0)))),
% 0.39/0.57      inference('simplify_reflect-', [status(thm)], ['102', '103'])).
% 0.39/0.57  thf('105', plain,
% 0.39/0.57      (![X6 : $i, X7 : $i]:
% 0.39/0.57         (((X6) = (o_0_0_xboole_0))
% 0.39/0.57          | ((k2_relat_1 @ (k2_zfmisc_1 @ X6 @ X7)) = (X7))
% 0.39/0.57          | ((X7) = (o_0_0_xboole_0)))),
% 0.39/0.57      inference('demod', [status(thm)], ['1', '2', '3'])).
% 0.39/0.57  thf('106', plain,
% 0.39/0.57      ((((k2_relat_1 @ o_0_0_xboole_0) = (sk_B))
% 0.39/0.57        | (v1_xboole_0 @ sk_C)
% 0.39/0.57        | ((sk_B) = (o_0_0_xboole_0))
% 0.39/0.57        | ((sk_A) = (o_0_0_xboole_0)))),
% 0.39/0.57      inference('sup+', [status(thm)], ['104', '105'])).
% 0.39/0.57  thf('107', plain,
% 0.39/0.57      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.39/0.57        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.39/0.57      inference('demod', [status(thm)], ['10', '13'])).
% 0.39/0.57  thf('108', plain,
% 0.39/0.57      (![X3 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X3)) | ~ (v1_xboole_0 @ X3))),
% 0.39/0.57      inference('cnf', [status(esa)], [fc11_relat_1])).
% 0.39/0.57  thf('109', plain,
% 0.39/0.57      (![X3 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X3)) | ~ (v1_xboole_0 @ X3))),
% 0.39/0.57      inference('cnf', [status(esa)], [fc11_relat_1])).
% 0.39/0.57  thf('110', plain,
% 0.39/0.57      (![X3 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X3)) | ~ (v1_xboole_0 @ X3))),
% 0.39/0.57      inference('cnf', [status(esa)], [fc11_relat_1])).
% 0.39/0.57  thf('111', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (~ (v1_xboole_0 @ X0) | ((k2_relat_1 @ X0) = (o_0_0_xboole_0)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['15', '18'])).
% 0.39/0.57  thf('112', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (~ (v1_xboole_0 @ X0)
% 0.39/0.57          | ((k2_relat_1 @ (k2_relat_1 @ X0)) = (o_0_0_xboole_0)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['110', '111'])).
% 0.39/0.57  thf('113', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (~ (v1_xboole_0 @ X0)
% 0.39/0.57          | ((k2_relat_1 @ (k2_relat_1 @ (k2_relat_1 @ X0))) = (o_0_0_xboole_0)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['109', '112'])).
% 0.39/0.57  thf('114', plain,
% 0.39/0.57      (![X3 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X3)) | ~ (v1_xboole_0 @ X3))),
% 0.39/0.57      inference('cnf', [status(esa)], [fc11_relat_1])).
% 0.39/0.57  thf('115', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((v1_xboole_0 @ o_0_0_xboole_0)
% 0.39/0.57          | ~ (v1_xboole_0 @ X0)
% 0.39/0.57          | ~ (v1_xboole_0 @ (k2_relat_1 @ (k2_relat_1 @ X0))))),
% 0.39/0.57      inference('sup+', [status(thm)], ['113', '114'])).
% 0.39/0.57  thf('116', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.39/0.57          | ~ (v1_xboole_0 @ X0)
% 0.39/0.57          | (v1_xboole_0 @ o_0_0_xboole_0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['108', '115'])).
% 0.39/0.57  thf('117', plain,
% 0.39/0.57      (![X3 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X3)) | ~ (v1_xboole_0 @ X3))),
% 0.39/0.57      inference('cnf', [status(esa)], [fc11_relat_1])).
% 0.39/0.57  thf('118', plain,
% 0.39/0.57      (![X0 : $i]: ((v1_xboole_0 @ o_0_0_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 0.39/0.57      inference('clc', [status(thm)], ['116', '117'])).
% 0.39/0.57  thf('119', plain,
% 0.39/0.57      ((((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.39/0.57        | (v1_xboole_0 @ o_0_0_xboole_0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['107', '118'])).
% 0.39/0.57  thf('120', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.39/0.57          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.39/0.57          | ((sk_D) = (X0))
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ sk_C))),
% 0.39/0.57      inference('demod', [status(thm)], ['59', '74'])).
% 0.39/0.57  thf('121', plain,
% 0.39/0.57      ((((sk_E) != (sk_E))
% 0.39/0.57        | (v1_xboole_0 @ o_0_0_xboole_0)
% 0.39/0.57        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)
% 0.39/0.57        | ((sk_D) = (k2_mcart_1 @ sk_E))
% 0.39/0.57        | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['119', '120'])).
% 0.39/0.57  thf('122', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)),
% 0.39/0.57      inference('demod', [status(thm)], ['79', '90'])).
% 0.39/0.57  thf('123', plain,
% 0.39/0.57      ((((sk_E) != (sk_E))
% 0.39/0.57        | (v1_xboole_0 @ o_0_0_xboole_0)
% 0.39/0.57        | ((sk_D) = (k2_mcart_1 @ sk_E))
% 0.39/0.57        | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 0.39/0.57      inference('demod', [status(thm)], ['121', '122'])).
% 0.39/0.57  thf('124', plain,
% 0.39/0.57      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.39/0.57        | ((sk_D) = (k2_mcart_1 @ sk_E))
% 0.39/0.57        | (v1_xboole_0 @ o_0_0_xboole_0))),
% 0.39/0.57      inference('simplify', [status(thm)], ['123'])).
% 0.39/0.57  thf('125', plain, (((sk_D) != (k2_mcart_1 @ sk_E))),
% 0.39/0.57      inference('demod', [status(thm)], ['94', '95'])).
% 0.39/0.57  thf('126', plain,
% 0.39/0.57      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.39/0.57        | (v1_xboole_0 @ o_0_0_xboole_0))),
% 0.39/0.57      inference('simplify_reflect-', [status(thm)], ['124', '125'])).
% 0.39/0.57  thf('127', plain,
% 0.39/0.57      (![X0 : $i]: ((v1_xboole_0 @ o_0_0_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 0.39/0.57      inference('clc', [status(thm)], ['116', '117'])).
% 0.39/0.57  thf('128', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 0.39/0.57      inference('clc', [status(thm)], ['126', '127'])).
% 0.39/0.57  thf('129', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (~ (v1_xboole_0 @ X0) | ((k2_relat_1 @ X0) = (o_0_0_xboole_0)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['15', '18'])).
% 0.39/0.57  thf('130', plain, (((k2_relat_1 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['128', '129'])).
% 0.39/0.57  thf('131', plain,
% 0.39/0.57      ((((o_0_0_xboole_0) = (sk_B))
% 0.39/0.57        | (v1_xboole_0 @ sk_C)
% 0.39/0.57        | ((sk_B) = (o_0_0_xboole_0))
% 0.39/0.57        | ((sk_A) = (o_0_0_xboole_0)))),
% 0.39/0.57      inference('demod', [status(thm)], ['106', '130'])).
% 0.39/0.57  thf('132', plain,
% 0.39/0.57      ((((sk_A) = (o_0_0_xboole_0))
% 0.39/0.57        | (v1_xboole_0 @ sk_C)
% 0.39/0.57        | ((o_0_0_xboole_0) = (sk_B)))),
% 0.39/0.57      inference('simplify', [status(thm)], ['131'])).
% 0.39/0.57  thf('133', plain, (((sk_B) != (o_0_0_xboole_0))),
% 0.39/0.57      inference('demod', [status(thm)], ['51', '52'])).
% 0.39/0.57  thf('134', plain, (((sk_A) != (o_0_0_xboole_0))),
% 0.39/0.57      inference('demod', [status(thm)], ['48', '49'])).
% 0.39/0.57  thf('135', plain, ((v1_xboole_0 @ sk_C)),
% 0.39/0.57      inference('simplify_reflect-', [status(thm)], ['132', '133', '134'])).
% 0.39/0.57  thf('136', plain,
% 0.39/0.57      (![X0 : $i]: (((X0) = (o_0_0_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.39/0.57      inference('demod', [status(thm)], ['16', '17'])).
% 0.39/0.57  thf('137', plain, (((sk_C) = (o_0_0_xboole_0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['135', '136'])).
% 0.39/0.57  thf('138', plain, (((sk_C) != (o_0_0_xboole_0))),
% 0.39/0.57      inference('demod', [status(thm)], ['23', '24'])).
% 0.39/0.57  thf('139', plain, ($false),
% 0.39/0.57      inference('simplify_reflect-', [status(thm)], ['137', '138'])).
% 0.39/0.57  
% 0.39/0.57  % SZS output end Refutation
% 0.39/0.57  
% 0.39/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
