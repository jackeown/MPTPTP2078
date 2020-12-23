%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.S8TxfN3wib

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:54 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 200 expanded)
%              Number of leaves         :   32 (  73 expanded)
%              Depth                    :   18
%              Number of atoms          : 1024 (3511 expanded)
%              Number of equality atoms :  124 ( 485 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

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

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t23_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( A
          = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X24
        = ( k4_tarski @ ( k1_mcart_1 @ X24 ) @ ( k2_mcart_1 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X25 )
      | ~ ( r2_hidden @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( v1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('10',plain,
    ( ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t35_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) )
    <=> ( ( k3_zfmisc_1 @ A @ B @ C )
       != k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k3_zfmisc_1 @ X26 @ X27 @ X28 )
       != k1_xboole_0 )
      | ( X28 = k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('12',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( sk_E
    = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['13','14','15','16'])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('19',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('20',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X21 ) @ X22 )
      | ~ ( r2_hidden @ X21 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X24
        = ( k4_tarski @ ( k1_mcart_1 @ X24 ) @ ( k2_mcart_1 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X25 )
      | ~ ( r2_hidden @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('26',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('27',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_mcart_1 @ X7 @ X8 @ X9 )
      = ( k4_tarski @ ( k4_tarski @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X0 )
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k6_mcart_1 @ A @ B @ C @ D ) @ B ) ) )).

thf('30',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( m1_subset_1 @ ( k6_mcart_1 @ X13 @ X14 @ X15 @ X16 ) @ X14 )
      | ~ ( m1_subset_1 @ X16 @ ( k3_zfmisc_1 @ X13 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_mcart_1])).

thf('31',plain,(
    m1_subset_1 @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_B ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
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

thf('33',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( X30 = k1_xboole_0 )
      | ( X31 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X30 @ X31 @ X33 @ X32 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k3_zfmisc_1 @ X30 @ X31 @ X33 ) )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('34',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['34','35','36','37'])).

thf('39',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B ),
    inference(demod,[status(thm)],['31','38'])).

thf('40',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ sk_B )
      | ( sk_D = X34 )
      | ( sk_E
       != ( k3_mcart_1 @ X35 @ X34 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ sk_C )
      | ~ ( m1_subset_1 @ X35 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_E
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 ) )
      | ( sk_D
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    sk_D
 != ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['34','35','36','37'])).

thf('44',plain,(
    sk_D
 != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_E
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','45'])).

thf('47',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('48',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X21 ) @ X22 )
      | ~ ( r2_hidden @ X21 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('49',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('51',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k3_zfmisc_1 @ X26 @ X27 @ X28 )
       != k1_xboole_0 )
      | ( X28 = k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('53',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['54','55','56','57'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('59',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X1 @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('60',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['46','60'])).

thf('62',plain,
    ( ( sk_E != sk_E )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ) )).

thf('64',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( m1_subset_1 @ ( k7_mcart_1 @ X17 @ X18 @ X19 @ X20 ) @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k3_zfmisc_1 @ X17 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_mcart_1])).

thf('65',plain,(
    m1_subset_1 @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_C ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( X30 = k1_xboole_0 )
      | ( X31 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X30 @ X31 @ X33 @ X32 )
        = ( k2_mcart_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k3_zfmisc_1 @ X30 @ X31 @ X33 ) )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('68',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k2_mcart_1 @ sk_E ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['68','69','70','71'])).

thf('73',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['65','72'])).

thf('74',plain,
    ( ( sk_E != sk_E )
    | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['62','73'])).

thf('75',plain,(
    v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('77',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k3_zfmisc_1 @ X26 @ X27 @ X28 )
       != k1_xboole_0 )
      | ( X28 = k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('79',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['80','81','82','83'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.S8TxfN3wib
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:33:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.90/1.08  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.90/1.08  % Solved by: fo/fo7.sh
% 0.90/1.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.08  % done 1278 iterations in 0.624s
% 0.90/1.08  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.90/1.08  % SZS output start Refutation
% 0.90/1.08  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.90/1.08  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.90/1.08  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.08  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.90/1.08  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.90/1.08  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.90/1.08  thf(sk_D_type, type, sk_D: $i).
% 0.90/1.08  thf(sk_C_type, type, sk_C: $i).
% 0.90/1.08  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.90/1.08  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.90/1.08  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.90/1.08  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.90/1.08  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.90/1.08  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.90/1.08  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.08  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.90/1.08  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.90/1.08  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.90/1.08  thf(sk_E_type, type, sk_E: $i).
% 0.90/1.08  thf(t70_mcart_1, conjecture,
% 0.90/1.08    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.90/1.08     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.90/1.08       ( ( ![F:$i]:
% 0.90/1.08           ( ( m1_subset_1 @ F @ A ) =>
% 0.90/1.08             ( ![G:$i]:
% 0.90/1.08               ( ( m1_subset_1 @ G @ B ) =>
% 0.90/1.08                 ( ![H:$i]:
% 0.90/1.08                   ( ( m1_subset_1 @ H @ C ) =>
% 0.90/1.08                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.90/1.08                       ( ( D ) = ( G ) ) ) ) ) ) ) ) ) =>
% 0.90/1.08         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.90/1.08           ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.90/1.08           ( ( D ) = ( k6_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 0.90/1.08  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.08    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.90/1.08        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.90/1.08          ( ( ![F:$i]:
% 0.90/1.08              ( ( m1_subset_1 @ F @ A ) =>
% 0.90/1.08                ( ![G:$i]:
% 0.90/1.08                  ( ( m1_subset_1 @ G @ B ) =>
% 0.90/1.08                    ( ![H:$i]:
% 0.90/1.08                      ( ( m1_subset_1 @ H @ C ) =>
% 0.90/1.08                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.90/1.08                          ( ( D ) = ( G ) ) ) ) ) ) ) ) ) =>
% 0.90/1.08            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.90/1.08              ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.90/1.08              ( ( D ) = ( k6_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 0.90/1.08    inference('cnf.neg', [status(esa)], [t70_mcart_1])).
% 0.90/1.08  thf('0', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf(t2_subset, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( m1_subset_1 @ A @ B ) =>
% 0.90/1.08       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.90/1.08  thf('1', plain,
% 0.90/1.08      (![X3 : $i, X4 : $i]:
% 0.90/1.08         ((r2_hidden @ X3 @ X4)
% 0.90/1.08          | (v1_xboole_0 @ X4)
% 0.90/1.08          | ~ (m1_subset_1 @ X3 @ X4))),
% 0.90/1.08      inference('cnf', [status(esa)], [t2_subset])).
% 0.90/1.08  thf('2', plain,
% 0.90/1.08      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.90/1.08        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['0', '1'])).
% 0.90/1.08  thf(t23_mcart_1, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( v1_relat_1 @ B ) =>
% 0.90/1.08       ( ( r2_hidden @ A @ B ) =>
% 0.90/1.08         ( ( A ) = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ))).
% 0.90/1.08  thf('3', plain,
% 0.90/1.08      (![X24 : $i, X25 : $i]:
% 0.90/1.08         (((X24) = (k4_tarski @ (k1_mcart_1 @ X24) @ (k2_mcart_1 @ X24)))
% 0.90/1.08          | ~ (v1_relat_1 @ X25)
% 0.90/1.08          | ~ (r2_hidden @ X24 @ X25))),
% 0.90/1.08      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.90/1.08  thf('4', plain,
% 0.90/1.08      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.90/1.08        | ~ (v1_relat_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.90/1.08        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.90/1.08      inference('sup-', [status(thm)], ['2', '3'])).
% 0.90/1.08  thf(d3_zfmisc_1, axiom,
% 0.90/1.08    (![A:$i,B:$i,C:$i]:
% 0.90/1.08     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.90/1.08       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.90/1.08  thf('5', plain,
% 0.90/1.08      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.90/1.08         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 0.90/1.08           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 0.90/1.08      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.90/1.08  thf(fc6_relat_1, axiom,
% 0.90/1.08    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.90/1.08  thf('6', plain,
% 0.90/1.08      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.90/1.08      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.90/1.08  thf('7', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.08         (v1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))),
% 0.90/1.08      inference('sup+', [status(thm)], ['5', '6'])).
% 0.90/1.08  thf('8', plain,
% 0.90/1.08      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.90/1.08        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.90/1.08      inference('demod', [status(thm)], ['4', '7'])).
% 0.90/1.08  thf(l13_xboole_0, axiom,
% 0.90/1.08    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.90/1.08  thf('9', plain,
% 0.90/1.08      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.08      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.90/1.08  thf('10', plain,
% 0.90/1.08      ((((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.90/1.08        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['8', '9'])).
% 0.90/1.08  thf(t35_mcart_1, axiom,
% 0.90/1.08    (![A:$i,B:$i,C:$i]:
% 0.90/1.08     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.90/1.08         ( ( C ) != ( k1_xboole_0 ) ) ) <=>
% 0.90/1.08       ( ( k3_zfmisc_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) ))).
% 0.90/1.08  thf('11', plain,
% 0.90/1.08      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.90/1.08         (((k3_zfmisc_1 @ X26 @ X27 @ X28) != (k1_xboole_0))
% 0.90/1.08          | ((X28) = (k1_xboole_0))
% 0.90/1.08          | ((X27) = (k1_xboole_0))
% 0.90/1.08          | ((X26) = (k1_xboole_0)))),
% 0.90/1.08      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.90/1.08  thf('12', plain,
% 0.90/1.08      ((((k1_xboole_0) != (k1_xboole_0))
% 0.90/1.08        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.90/1.08        | ((sk_A) = (k1_xboole_0))
% 0.90/1.08        | ((sk_B) = (k1_xboole_0))
% 0.90/1.08        | ((sk_C) = (k1_xboole_0)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['10', '11'])).
% 0.90/1.08  thf('13', plain,
% 0.90/1.08      ((((sk_C) = (k1_xboole_0))
% 0.90/1.08        | ((sk_B) = (k1_xboole_0))
% 0.90/1.08        | ((sk_A) = (k1_xboole_0))
% 0.90/1.08        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.90/1.08      inference('simplify', [status(thm)], ['12'])).
% 0.90/1.08  thf('14', plain, (((sk_A) != (k1_xboole_0))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('15', plain, (((sk_B) != (k1_xboole_0))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('16', plain, (((sk_C) != (k1_xboole_0))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('17', plain,
% 0.90/1.08      (((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))),
% 0.90/1.08      inference('simplify_reflect-', [status(thm)], ['13', '14', '15', '16'])).
% 0.90/1.08  thf('18', plain,
% 0.90/1.08      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.90/1.08        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['0', '1'])).
% 0.90/1.08  thf('19', plain,
% 0.90/1.08      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.90/1.08         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 0.90/1.08           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 0.90/1.08      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.90/1.08  thf(t10_mcart_1, axiom,
% 0.90/1.08    (![A:$i,B:$i,C:$i]:
% 0.90/1.08     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.90/1.08       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.90/1.08         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.90/1.08  thf('20', plain,
% 0.90/1.08      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.90/1.08         ((r2_hidden @ (k1_mcart_1 @ X21) @ X22)
% 0.90/1.08          | ~ (r2_hidden @ X21 @ (k2_zfmisc_1 @ X22 @ X23)))),
% 0.90/1.08      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.90/1.08  thf('21', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.90/1.08         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.90/1.08          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['19', '20'])).
% 0.90/1.08  thf('22', plain,
% 0.90/1.08      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.90/1.08        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['18', '21'])).
% 0.90/1.08  thf('23', plain,
% 0.90/1.08      (![X24 : $i, X25 : $i]:
% 0.90/1.08         (((X24) = (k4_tarski @ (k1_mcart_1 @ X24) @ (k2_mcart_1 @ X24)))
% 0.90/1.08          | ~ (v1_relat_1 @ X25)
% 0.90/1.08          | ~ (r2_hidden @ X24 @ X25))),
% 0.90/1.08      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.90/1.08  thf('24', plain,
% 0.90/1.08      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.90/1.08        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.90/1.08        | ((k1_mcart_1 @ sk_E)
% 0.90/1.08            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.90/1.08               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 0.90/1.08      inference('sup-', [status(thm)], ['22', '23'])).
% 0.90/1.08  thf('25', plain,
% 0.90/1.08      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.90/1.08      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.90/1.08  thf('26', plain,
% 0.90/1.08      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.90/1.08        | ((k1_mcart_1 @ sk_E)
% 0.90/1.08            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.90/1.08               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 0.90/1.08      inference('demod', [status(thm)], ['24', '25'])).
% 0.90/1.08  thf(d3_mcart_1, axiom,
% 0.90/1.08    (![A:$i,B:$i,C:$i]:
% 0.90/1.08     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.90/1.08  thf('27', plain,
% 0.90/1.08      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.90/1.08         ((k3_mcart_1 @ X7 @ X8 @ X9)
% 0.90/1.08           = (k4_tarski @ (k4_tarski @ X7 @ X8) @ X9))),
% 0.90/1.08      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.90/1.08  thf('28', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         (((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.90/1.08            (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X0)
% 0.90/1.08            = (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.90/1.08          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 0.90/1.08      inference('sup+', [status(thm)], ['26', '27'])).
% 0.90/1.08  thf('29', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf(dt_k6_mcart_1, axiom,
% 0.90/1.08    (![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.08     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.90/1.08       ( m1_subset_1 @ ( k6_mcart_1 @ A @ B @ C @ D ) @ B ) ))).
% 0.90/1.08  thf('30', plain,
% 0.90/1.08      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.90/1.08         ((m1_subset_1 @ (k6_mcart_1 @ X13 @ X14 @ X15 @ X16) @ X14)
% 0.90/1.08          | ~ (m1_subset_1 @ X16 @ (k3_zfmisc_1 @ X13 @ X14 @ X15)))),
% 0.90/1.08      inference('cnf', [status(esa)], [dt_k6_mcart_1])).
% 0.90/1.08  thf('31', plain,
% 0.90/1.08      ((m1_subset_1 @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_B)),
% 0.90/1.08      inference('sup-', [status(thm)], ['29', '30'])).
% 0.90/1.08  thf('32', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf(t50_mcart_1, axiom,
% 0.90/1.08    (![A:$i,B:$i,C:$i]:
% 0.90/1.08     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.90/1.08          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.90/1.08          ( ~( ![D:$i]:
% 0.90/1.08               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.90/1.08                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.90/1.08                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.90/1.08                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.90/1.08                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.90/1.08                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.90/1.08  thf('33', plain,
% 0.90/1.08      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.90/1.08         (((X30) = (k1_xboole_0))
% 0.90/1.08          | ((X31) = (k1_xboole_0))
% 0.90/1.08          | ((k6_mcart_1 @ X30 @ X31 @ X33 @ X32)
% 0.90/1.08              = (k2_mcart_1 @ (k1_mcart_1 @ X32)))
% 0.90/1.08          | ~ (m1_subset_1 @ X32 @ (k3_zfmisc_1 @ X30 @ X31 @ X33))
% 0.90/1.08          | ((X33) = (k1_xboole_0)))),
% 0.90/1.08      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.90/1.08  thf('34', plain,
% 0.90/1.08      ((((sk_C) = (k1_xboole_0))
% 0.90/1.08        | ((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.90/1.08            = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.90/1.08        | ((sk_B) = (k1_xboole_0))
% 0.90/1.08        | ((sk_A) = (k1_xboole_0)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['32', '33'])).
% 0.90/1.08  thf('35', plain, (((sk_A) != (k1_xboole_0))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('36', plain, (((sk_B) != (k1_xboole_0))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('37', plain, (((sk_C) != (k1_xboole_0))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('38', plain,
% 0.90/1.08      (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.90/1.08         = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 0.90/1.08      inference('simplify_reflect-', [status(thm)], ['34', '35', '36', '37'])).
% 0.90/1.08  thf('39', plain, ((m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B)),
% 0.90/1.08      inference('demod', [status(thm)], ['31', '38'])).
% 0.90/1.08  thf('40', plain,
% 0.90/1.08      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.90/1.08         (~ (m1_subset_1 @ X34 @ sk_B)
% 0.90/1.08          | ((sk_D) = (X34))
% 0.90/1.08          | ((sk_E) != (k3_mcart_1 @ X35 @ X34 @ X36))
% 0.90/1.08          | ~ (m1_subset_1 @ X36 @ sk_C)
% 0.90/1.08          | ~ (m1_subset_1 @ X35 @ sk_A))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('41', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.90/1.08          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.90/1.08          | ((sk_E)
% 0.90/1.08              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1))
% 0.90/1.08          | ((sk_D) = (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 0.90/1.08      inference('sup-', [status(thm)], ['39', '40'])).
% 0.90/1.08  thf('42', plain, (((sk_D) != (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('43', plain,
% 0.90/1.08      (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.90/1.08         = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 0.90/1.08      inference('simplify_reflect-', [status(thm)], ['34', '35', '36', '37'])).
% 0.90/1.08  thf('44', plain, (((sk_D) != (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 0.90/1.08      inference('demod', [status(thm)], ['42', '43'])).
% 0.90/1.08  thf('45', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.90/1.08          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.90/1.08          | ((sk_E)
% 0.90/1.08              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1)))),
% 0.90/1.08      inference('simplify_reflect-', [status(thm)], ['41', '44'])).
% 0.90/1.08  thf('46', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.90/1.08          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.90/1.08          | ~ (m1_subset_1 @ X0 @ sk_C)
% 0.90/1.08          | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.90/1.08      inference('sup-', [status(thm)], ['28', '45'])).
% 0.90/1.08  thf('47', plain,
% 0.90/1.08      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.90/1.08        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['18', '21'])).
% 0.90/1.08  thf('48', plain,
% 0.90/1.08      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.90/1.08         ((r2_hidden @ (k1_mcart_1 @ X21) @ X22)
% 0.90/1.08          | ~ (r2_hidden @ X21 @ (k2_zfmisc_1 @ X22 @ X23)))),
% 0.90/1.08      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.90/1.08  thf('49', plain,
% 0.90/1.08      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.90/1.08        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.90/1.08      inference('sup-', [status(thm)], ['47', '48'])).
% 0.90/1.08  thf('50', plain,
% 0.90/1.08      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.08      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.90/1.08  thf('51', plain,
% 0.90/1.08      (((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 0.90/1.08        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['49', '50'])).
% 0.90/1.08  thf('52', plain,
% 0.90/1.08      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.90/1.08         (((k3_zfmisc_1 @ X26 @ X27 @ X28) != (k1_xboole_0))
% 0.90/1.08          | ((X28) = (k1_xboole_0))
% 0.90/1.08          | ((X27) = (k1_xboole_0))
% 0.90/1.08          | ((X26) = (k1_xboole_0)))),
% 0.90/1.08      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.90/1.08  thf('53', plain,
% 0.90/1.08      ((((k1_xboole_0) != (k1_xboole_0))
% 0.90/1.08        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 0.90/1.08        | ((sk_A) = (k1_xboole_0))
% 0.90/1.08        | ((sk_B) = (k1_xboole_0))
% 0.90/1.08        | ((sk_C) = (k1_xboole_0)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['51', '52'])).
% 0.90/1.08  thf('54', plain,
% 0.90/1.08      ((((sk_C) = (k1_xboole_0))
% 0.90/1.08        | ((sk_B) = (k1_xboole_0))
% 0.90/1.08        | ((sk_A) = (k1_xboole_0))
% 0.90/1.08        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.90/1.08      inference('simplify', [status(thm)], ['53'])).
% 0.90/1.08  thf('55', plain, (((sk_A) != (k1_xboole_0))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('56', plain, (((sk_B) != (k1_xboole_0))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('57', plain, (((sk_C) != (k1_xboole_0))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('58', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)),
% 0.90/1.08      inference('simplify_reflect-', [status(thm)], ['54', '55', '56', '57'])).
% 0.90/1.08  thf(t1_subset, axiom,
% 0.90/1.08    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.90/1.08  thf('59', plain,
% 0.90/1.08      (![X1 : $i, X2 : $i]: ((m1_subset_1 @ X1 @ X2) | ~ (r2_hidden @ X1 @ X2))),
% 0.90/1.08      inference('cnf', [status(esa)], [t1_subset])).
% 0.90/1.08  thf('60', plain, ((m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)),
% 0.90/1.08      inference('sup-', [status(thm)], ['58', '59'])).
% 0.90/1.08  thf('61', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.90/1.08          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.90/1.08          | ~ (m1_subset_1 @ X0 @ sk_C))),
% 0.90/1.08      inference('demod', [status(thm)], ['46', '60'])).
% 0.90/1.08  thf('62', plain,
% 0.90/1.08      ((((sk_E) != (sk_E))
% 0.90/1.08        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)
% 0.90/1.08        | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['17', '61'])).
% 0.90/1.08  thf('63', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf(dt_k7_mcart_1, axiom,
% 0.90/1.08    (![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.08     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.90/1.08       ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ))).
% 0.90/1.08  thf('64', plain,
% 0.90/1.08      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.90/1.08         ((m1_subset_1 @ (k7_mcart_1 @ X17 @ X18 @ X19 @ X20) @ X19)
% 0.90/1.08          | ~ (m1_subset_1 @ X20 @ (k3_zfmisc_1 @ X17 @ X18 @ X19)))),
% 0.90/1.08      inference('cnf', [status(esa)], [dt_k7_mcart_1])).
% 0.90/1.08  thf('65', plain,
% 0.90/1.08      ((m1_subset_1 @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_C)),
% 0.90/1.08      inference('sup-', [status(thm)], ['63', '64'])).
% 0.90/1.08  thf('66', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('67', plain,
% 0.90/1.08      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.90/1.08         (((X30) = (k1_xboole_0))
% 0.90/1.08          | ((X31) = (k1_xboole_0))
% 0.90/1.08          | ((k7_mcart_1 @ X30 @ X31 @ X33 @ X32) = (k2_mcart_1 @ X32))
% 0.90/1.08          | ~ (m1_subset_1 @ X32 @ (k3_zfmisc_1 @ X30 @ X31 @ X33))
% 0.90/1.08          | ((X33) = (k1_xboole_0)))),
% 0.90/1.08      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.90/1.08  thf('68', plain,
% 0.90/1.08      ((((sk_C) = (k1_xboole_0))
% 0.90/1.08        | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))
% 0.90/1.08        | ((sk_B) = (k1_xboole_0))
% 0.90/1.08        | ((sk_A) = (k1_xboole_0)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['66', '67'])).
% 0.90/1.08  thf('69', plain, (((sk_A) != (k1_xboole_0))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('70', plain, (((sk_B) != (k1_xboole_0))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('71', plain, (((sk_C) != (k1_xboole_0))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('72', plain,
% 0.90/1.08      (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))),
% 0.90/1.08      inference('simplify_reflect-', [status(thm)], ['68', '69', '70', '71'])).
% 0.90/1.08  thf('73', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)),
% 0.90/1.08      inference('demod', [status(thm)], ['65', '72'])).
% 0.90/1.08  thf('74', plain,
% 0.90/1.08      ((((sk_E) != (sk_E)) | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 0.90/1.08      inference('demod', [status(thm)], ['62', '73'])).
% 0.90/1.08  thf('75', plain, ((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.90/1.08      inference('simplify', [status(thm)], ['74'])).
% 0.90/1.08  thf('76', plain,
% 0.90/1.08      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.08      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.90/1.08  thf('77', plain, (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))),
% 0.90/1.08      inference('sup-', [status(thm)], ['75', '76'])).
% 0.90/1.08  thf('78', plain,
% 0.90/1.08      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.90/1.08         (((k3_zfmisc_1 @ X26 @ X27 @ X28) != (k1_xboole_0))
% 0.90/1.08          | ((X28) = (k1_xboole_0))
% 0.90/1.08          | ((X27) = (k1_xboole_0))
% 0.90/1.08          | ((X26) = (k1_xboole_0)))),
% 0.90/1.08      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.90/1.08  thf('79', plain,
% 0.90/1.08      ((((k1_xboole_0) != (k1_xboole_0))
% 0.90/1.08        | ((sk_A) = (k1_xboole_0))
% 0.90/1.08        | ((sk_B) = (k1_xboole_0))
% 0.90/1.08        | ((sk_C) = (k1_xboole_0)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['77', '78'])).
% 0.90/1.08  thf('80', plain,
% 0.90/1.08      ((((sk_C) = (k1_xboole_0))
% 0.90/1.08        | ((sk_B) = (k1_xboole_0))
% 0.90/1.08        | ((sk_A) = (k1_xboole_0)))),
% 0.90/1.08      inference('simplify', [status(thm)], ['79'])).
% 0.90/1.08  thf('81', plain, (((sk_A) != (k1_xboole_0))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('82', plain, (((sk_B) != (k1_xboole_0))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('83', plain, (((sk_C) != (k1_xboole_0))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('84', plain, ($false),
% 0.90/1.08      inference('simplify_reflect-', [status(thm)], ['80', '81', '82', '83'])).
% 0.90/1.08  
% 0.90/1.08  % SZS output end Refutation
% 0.90/1.08  
% 0.90/1.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
