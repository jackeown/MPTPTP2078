%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.01l483sp3q

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:00 EST 2020

% Result     : Theorem 0.89s
% Output     : Refutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 188 expanded)
%              Number of leaves         :   32 (  69 expanded)
%              Depth                    :   17
%              Number of atoms          : 1016 (3502 expanded)
%              Number of equality atoms :  124 ( 496 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

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
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X2 )
      | ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ X2 ) ) ),
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
    ! [X26: $i,X27: $i] :
      ( ( X26
        = ( k4_tarski @ ( k1_mcart_1 @ X26 ) @ ( k2_mcart_1 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X27 )
      | ~ ( r2_hidden @ X26 @ X27 ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_zfmisc_1 @ X8 @ X9 @ X10 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k3_zfmisc_1 @ X28 @ X29 @ X30 )
       != k1_xboole_0 )
      | ( X30 = k1_xboole_0 )
      | ( X29 = k1_xboole_0 )
      | ( X28 = k1_xboole_0 ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_zfmisc_1 @ X8 @ X9 @ X10 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('20',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X23 ) @ X24 )
      | ~ ( r2_hidden @ X23 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ),
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
    ! [X26: $i,X27: $i] :
      ( ( X26
        = ( k4_tarski @ ( k1_mcart_1 @ X26 ) @ ( k2_mcart_1 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X27 )
      | ~ ( r2_hidden @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X3: $i,X4: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
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
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_mcart_1 @ X5 @ X6 @ X7 )
      = ( k4_tarski @ ( k4_tarski @ X5 @ X6 ) @ X7 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( m1_subset_1 @ ( k6_mcart_1 @ X15 @ X16 @ X17 @ X18 ) @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( k3_zfmisc_1 @ X15 @ X16 @ X17 ) ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( X32 = k1_xboole_0 )
      | ( X33 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X32 @ X33 @ X35 @ X34 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k3_zfmisc_1 @ X32 @ X33 @ X35 ) )
      | ( X35 = k1_xboole_0 ) ) ),
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
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X36 @ sk_B )
      | ( sk_E
       != ( k3_mcart_1 @ X37 @ X36 @ X38 ) )
      | ( sk_D = X38 )
      | ~ ( m1_subset_1 @ X38 @ sk_C )
      | ~ ( m1_subset_1 @ X37 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_D = X1 )
      | ( sk_E
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ A ) ) )).

thf('44',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k5_mcart_1 @ X11 @ X12 @ X13 @ X14 ) @ X11 )
      | ~ ( m1_subset_1 @ X14 @ ( k3_zfmisc_1 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_mcart_1])).

thf('45',plain,(
    m1_subset_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_A ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( X32 = k1_xboole_0 )
      | ( X33 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X32 @ X33 @ X35 @ X34 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k3_zfmisc_1 @ X32 @ X33 @ X35 ) )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('48',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['48','49','50','51'])).

thf('53',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ),
    inference(demod,[status(thm)],['45','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['42','53'])).

thf('55',plain,
    ( ( sk_E != sk_E )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) )
    | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ) )).

thf('57',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( m1_subset_1 @ ( k7_mcart_1 @ X19 @ X20 @ X21 @ X22 ) @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k3_zfmisc_1 @ X19 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_mcart_1])).

thf('58',plain,(
    m1_subset_1 @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_C ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( X32 = k1_xboole_0 )
      | ( X33 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X32 @ X33 @ X35 @ X34 )
        = ( k2_mcart_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k3_zfmisc_1 @ X32 @ X33 @ X35 ) )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('61',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k2_mcart_1 @ sk_E ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['61','62','63','64'])).

thf('66',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['58','65'])).

thf('67',plain,
    ( ( sk_E != sk_E )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) )
    | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['55','66'])).

thf('68',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    sk_D
 != ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['61','62','63','64'])).

thf('71',plain,(
    sk_D
 != ( k2_mcart_1 @ sk_E ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('74',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k3_zfmisc_1 @ X28 @ X29 @ X30 )
       != k1_xboole_0 )
      | ( X30 = k1_xboole_0 )
      | ( X29 = k1_xboole_0 )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('76',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['77','78','79','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.01l483sp3q
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:21:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.89/1.10  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.89/1.10  % Solved by: fo/fo7.sh
% 0.89/1.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.89/1.10  % done 1392 iterations in 0.651s
% 0.89/1.10  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.89/1.10  % SZS output start Refutation
% 0.89/1.10  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.89/1.10  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.89/1.10  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.89/1.10  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.89/1.10  thf(sk_D_type, type, sk_D: $i).
% 0.89/1.10  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.89/1.10  thf(sk_E_type, type, sk_E: $i).
% 0.89/1.10  thf(sk_B_type, type, sk_B: $i).
% 0.89/1.10  thf(sk_C_type, type, sk_C: $i).
% 0.89/1.10  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.89/1.10  thf(sk_A_type, type, sk_A: $i).
% 0.89/1.10  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.89/1.10  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.89/1.10  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.89/1.10  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.89/1.10  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.89/1.10  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.89/1.10  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.89/1.10  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.89/1.10  thf(t71_mcart_1, conjecture,
% 0.89/1.10    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.89/1.10     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.89/1.10       ( ( ![F:$i]:
% 0.89/1.10           ( ( m1_subset_1 @ F @ A ) =>
% 0.89/1.10             ( ![G:$i]:
% 0.89/1.10               ( ( m1_subset_1 @ G @ B ) =>
% 0.89/1.10                 ( ![H:$i]:
% 0.89/1.10                   ( ( m1_subset_1 @ H @ C ) =>
% 0.89/1.10                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.89/1.10                       ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 0.89/1.10         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.89/1.10           ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.89/1.10           ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 0.89/1.10  thf(zf_stmt_0, negated_conjecture,
% 0.89/1.10    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.89/1.10        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.89/1.10          ( ( ![F:$i]:
% 0.89/1.10              ( ( m1_subset_1 @ F @ A ) =>
% 0.89/1.10                ( ![G:$i]:
% 0.89/1.10                  ( ( m1_subset_1 @ G @ B ) =>
% 0.89/1.10                    ( ![H:$i]:
% 0.89/1.10                      ( ( m1_subset_1 @ H @ C ) =>
% 0.89/1.10                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.89/1.10                          ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 0.89/1.10            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.89/1.10              ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.89/1.10              ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 0.89/1.10    inference('cnf.neg', [status(esa)], [t71_mcart_1])).
% 0.89/1.10  thf('0', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.89/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.10  thf(t2_subset, axiom,
% 0.89/1.10    (![A:$i,B:$i]:
% 0.89/1.10     ( ( m1_subset_1 @ A @ B ) =>
% 0.89/1.10       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.89/1.10  thf('1', plain,
% 0.89/1.10      (![X1 : $i, X2 : $i]:
% 0.89/1.10         ((r2_hidden @ X1 @ X2)
% 0.89/1.10          | (v1_xboole_0 @ X2)
% 0.89/1.10          | ~ (m1_subset_1 @ X1 @ X2))),
% 0.89/1.10      inference('cnf', [status(esa)], [t2_subset])).
% 0.89/1.10  thf('2', plain,
% 0.89/1.10      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.89/1.10        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 0.89/1.10      inference('sup-', [status(thm)], ['0', '1'])).
% 0.89/1.10  thf(t23_mcart_1, axiom,
% 0.89/1.10    (![A:$i,B:$i]:
% 0.89/1.10     ( ( v1_relat_1 @ B ) =>
% 0.89/1.10       ( ( r2_hidden @ A @ B ) =>
% 0.89/1.10         ( ( A ) = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ))).
% 0.89/1.10  thf('3', plain,
% 0.89/1.10      (![X26 : $i, X27 : $i]:
% 0.89/1.10         (((X26) = (k4_tarski @ (k1_mcart_1 @ X26) @ (k2_mcart_1 @ X26)))
% 0.89/1.10          | ~ (v1_relat_1 @ X27)
% 0.89/1.10          | ~ (r2_hidden @ X26 @ X27))),
% 0.89/1.10      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.89/1.10  thf('4', plain,
% 0.89/1.10      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.89/1.10        | ~ (v1_relat_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.89/1.10        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.89/1.10      inference('sup-', [status(thm)], ['2', '3'])).
% 0.89/1.10  thf(d3_zfmisc_1, axiom,
% 0.89/1.10    (![A:$i,B:$i,C:$i]:
% 0.89/1.10     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.89/1.10       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.89/1.10  thf('5', plain,
% 0.89/1.10      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.89/1.10         ((k3_zfmisc_1 @ X8 @ X9 @ X10)
% 0.89/1.10           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9) @ X10))),
% 0.89/1.10      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.89/1.10  thf(fc6_relat_1, axiom,
% 0.89/1.10    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.89/1.10  thf('6', plain,
% 0.89/1.10      (![X3 : $i, X4 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X3 @ X4))),
% 0.89/1.10      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.89/1.10  thf('7', plain,
% 0.89/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.10         (v1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))),
% 0.89/1.10      inference('sup+', [status(thm)], ['5', '6'])).
% 0.89/1.10  thf('8', plain,
% 0.89/1.10      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.89/1.10        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.89/1.10      inference('demod', [status(thm)], ['4', '7'])).
% 0.89/1.10  thf(l13_xboole_0, axiom,
% 0.89/1.10    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.89/1.10  thf('9', plain,
% 0.89/1.10      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.89/1.10      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.89/1.10  thf('10', plain,
% 0.89/1.10      ((((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.89/1.10        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 0.89/1.10      inference('sup-', [status(thm)], ['8', '9'])).
% 0.89/1.10  thf(t35_mcart_1, axiom,
% 0.89/1.10    (![A:$i,B:$i,C:$i]:
% 0.89/1.10     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.89/1.10         ( ( C ) != ( k1_xboole_0 ) ) ) <=>
% 0.89/1.10       ( ( k3_zfmisc_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) ))).
% 0.89/1.10  thf('11', plain,
% 0.89/1.10      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.89/1.10         (((k3_zfmisc_1 @ X28 @ X29 @ X30) != (k1_xboole_0))
% 0.89/1.10          | ((X30) = (k1_xboole_0))
% 0.89/1.10          | ((X29) = (k1_xboole_0))
% 0.89/1.10          | ((X28) = (k1_xboole_0)))),
% 0.89/1.10      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.89/1.10  thf('12', plain,
% 0.89/1.10      ((((k1_xboole_0) != (k1_xboole_0))
% 0.89/1.10        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.89/1.10        | ((sk_A) = (k1_xboole_0))
% 0.89/1.10        | ((sk_B) = (k1_xboole_0))
% 0.89/1.10        | ((sk_C) = (k1_xboole_0)))),
% 0.89/1.10      inference('sup-', [status(thm)], ['10', '11'])).
% 0.89/1.10  thf('13', plain,
% 0.89/1.10      ((((sk_C) = (k1_xboole_0))
% 0.89/1.10        | ((sk_B) = (k1_xboole_0))
% 0.89/1.10        | ((sk_A) = (k1_xboole_0))
% 0.89/1.10        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.89/1.10      inference('simplify', [status(thm)], ['12'])).
% 0.89/1.10  thf('14', plain, (((sk_A) != (k1_xboole_0))),
% 0.89/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.10  thf('15', plain, (((sk_B) != (k1_xboole_0))),
% 0.89/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.10  thf('16', plain, (((sk_C) != (k1_xboole_0))),
% 0.89/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.10  thf('17', plain,
% 0.89/1.10      (((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))),
% 0.89/1.10      inference('simplify_reflect-', [status(thm)], ['13', '14', '15', '16'])).
% 0.89/1.10  thf('18', plain,
% 0.89/1.10      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.89/1.10        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 0.89/1.10      inference('sup-', [status(thm)], ['0', '1'])).
% 0.89/1.10  thf('19', plain,
% 0.89/1.10      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.89/1.10         ((k3_zfmisc_1 @ X8 @ X9 @ X10)
% 0.89/1.10           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9) @ X10))),
% 0.89/1.10      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.89/1.10  thf(t10_mcart_1, axiom,
% 0.89/1.10    (![A:$i,B:$i,C:$i]:
% 0.89/1.10     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.89/1.10       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.89/1.10         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.89/1.10  thf('20', plain,
% 0.89/1.10      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.89/1.10         ((r2_hidden @ (k1_mcart_1 @ X23) @ X24)
% 0.89/1.10          | ~ (r2_hidden @ X23 @ (k2_zfmisc_1 @ X24 @ X25)))),
% 0.89/1.10      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.89/1.10  thf('21', plain,
% 0.89/1.10      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.89/1.10         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.89/1.10          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.89/1.10      inference('sup-', [status(thm)], ['19', '20'])).
% 0.89/1.10  thf('22', plain,
% 0.89/1.10      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.89/1.10        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.10      inference('sup-', [status(thm)], ['18', '21'])).
% 0.89/1.10  thf('23', plain,
% 0.89/1.10      (![X26 : $i, X27 : $i]:
% 0.89/1.10         (((X26) = (k4_tarski @ (k1_mcart_1 @ X26) @ (k2_mcart_1 @ X26)))
% 0.89/1.10          | ~ (v1_relat_1 @ X27)
% 0.89/1.10          | ~ (r2_hidden @ X26 @ X27))),
% 0.89/1.10      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.89/1.10  thf('24', plain,
% 0.89/1.10      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.89/1.10        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.89/1.10        | ((k1_mcart_1 @ sk_E)
% 0.89/1.10            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.89/1.10               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 0.89/1.10      inference('sup-', [status(thm)], ['22', '23'])).
% 0.89/1.10  thf('25', plain,
% 0.89/1.10      (![X3 : $i, X4 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X3 @ X4))),
% 0.89/1.10      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.89/1.10  thf('26', plain,
% 0.89/1.10      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.89/1.10        | ((k1_mcart_1 @ sk_E)
% 0.89/1.10            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.89/1.10               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 0.89/1.10      inference('demod', [status(thm)], ['24', '25'])).
% 0.89/1.10  thf(d3_mcart_1, axiom,
% 0.89/1.10    (![A:$i,B:$i,C:$i]:
% 0.89/1.10     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.89/1.10  thf('27', plain,
% 0.89/1.10      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.89/1.10         ((k3_mcart_1 @ X5 @ X6 @ X7)
% 0.89/1.10           = (k4_tarski @ (k4_tarski @ X5 @ X6) @ X7))),
% 0.89/1.10      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.89/1.10  thf('28', plain,
% 0.89/1.10      (![X0 : $i]:
% 0.89/1.10         (((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.89/1.10            (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X0)
% 0.89/1.10            = (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.89/1.10          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 0.89/1.10      inference('sup+', [status(thm)], ['26', '27'])).
% 0.89/1.10  thf('29', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.89/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.10  thf(dt_k6_mcart_1, axiom,
% 0.89/1.10    (![A:$i,B:$i,C:$i,D:$i]:
% 0.89/1.10     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.89/1.10       ( m1_subset_1 @ ( k6_mcart_1 @ A @ B @ C @ D ) @ B ) ))).
% 0.89/1.10  thf('30', plain,
% 0.89/1.10      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.89/1.10         ((m1_subset_1 @ (k6_mcart_1 @ X15 @ X16 @ X17 @ X18) @ X16)
% 0.89/1.10          | ~ (m1_subset_1 @ X18 @ (k3_zfmisc_1 @ X15 @ X16 @ X17)))),
% 0.89/1.10      inference('cnf', [status(esa)], [dt_k6_mcart_1])).
% 0.89/1.10  thf('31', plain,
% 0.89/1.10      ((m1_subset_1 @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_B)),
% 0.89/1.10      inference('sup-', [status(thm)], ['29', '30'])).
% 0.89/1.10  thf('32', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.89/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.10  thf(t50_mcart_1, axiom,
% 0.89/1.10    (![A:$i,B:$i,C:$i]:
% 0.89/1.10     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.89/1.10          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.89/1.10          ( ~( ![D:$i]:
% 0.89/1.10               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.89/1.10                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.89/1.10                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.89/1.10                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.89/1.10                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.89/1.10                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.89/1.10  thf('33', plain,
% 0.89/1.10      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.89/1.10         (((X32) = (k1_xboole_0))
% 0.89/1.10          | ((X33) = (k1_xboole_0))
% 0.89/1.10          | ((k6_mcart_1 @ X32 @ X33 @ X35 @ X34)
% 0.89/1.10              = (k2_mcart_1 @ (k1_mcart_1 @ X34)))
% 0.89/1.10          | ~ (m1_subset_1 @ X34 @ (k3_zfmisc_1 @ X32 @ X33 @ X35))
% 0.89/1.10          | ((X35) = (k1_xboole_0)))),
% 0.89/1.10      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.89/1.10  thf('34', plain,
% 0.89/1.10      ((((sk_C) = (k1_xboole_0))
% 0.89/1.10        | ((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.89/1.10            = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.89/1.10        | ((sk_B) = (k1_xboole_0))
% 0.89/1.10        | ((sk_A) = (k1_xboole_0)))),
% 0.89/1.10      inference('sup-', [status(thm)], ['32', '33'])).
% 0.89/1.10  thf('35', plain, (((sk_A) != (k1_xboole_0))),
% 0.89/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.10  thf('36', plain, (((sk_B) != (k1_xboole_0))),
% 0.89/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.10  thf('37', plain, (((sk_C) != (k1_xboole_0))),
% 0.89/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.10  thf('38', plain,
% 0.89/1.10      (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.89/1.10         = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 0.89/1.10      inference('simplify_reflect-', [status(thm)], ['34', '35', '36', '37'])).
% 0.89/1.10  thf('39', plain, ((m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B)),
% 0.89/1.10      inference('demod', [status(thm)], ['31', '38'])).
% 0.89/1.10  thf('40', plain,
% 0.89/1.10      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.89/1.10         (~ (m1_subset_1 @ X36 @ sk_B)
% 0.89/1.10          | ((sk_E) != (k3_mcart_1 @ X37 @ X36 @ X38))
% 0.89/1.10          | ((sk_D) = (X38))
% 0.89/1.10          | ~ (m1_subset_1 @ X38 @ sk_C)
% 0.89/1.10          | ~ (m1_subset_1 @ X37 @ sk_A))),
% 0.89/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.10  thf('41', plain,
% 0.89/1.10      (![X0 : $i, X1 : $i]:
% 0.89/1.10         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.89/1.10          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.89/1.10          | ((sk_D) = (X1))
% 0.89/1.10          | ((sk_E)
% 0.89/1.10              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1)))),
% 0.89/1.10      inference('sup-', [status(thm)], ['39', '40'])).
% 0.89/1.10  thf('42', plain,
% 0.89/1.10      (![X0 : $i]:
% 0.89/1.10         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.89/1.10          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.89/1.10          | ((sk_D) = (X0))
% 0.89/1.10          | ~ (m1_subset_1 @ X0 @ sk_C)
% 0.89/1.10          | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.89/1.10      inference('sup-', [status(thm)], ['28', '41'])).
% 0.89/1.10  thf('43', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.89/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.10  thf(dt_k5_mcart_1, axiom,
% 0.89/1.10    (![A:$i,B:$i,C:$i,D:$i]:
% 0.89/1.10     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.89/1.10       ( m1_subset_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ A ) ))).
% 0.89/1.10  thf('44', plain,
% 0.89/1.10      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.89/1.10         ((m1_subset_1 @ (k5_mcart_1 @ X11 @ X12 @ X13 @ X14) @ X11)
% 0.89/1.10          | ~ (m1_subset_1 @ X14 @ (k3_zfmisc_1 @ X11 @ X12 @ X13)))),
% 0.89/1.10      inference('cnf', [status(esa)], [dt_k5_mcart_1])).
% 0.89/1.10  thf('45', plain,
% 0.89/1.10      ((m1_subset_1 @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_A)),
% 0.89/1.10      inference('sup-', [status(thm)], ['43', '44'])).
% 0.89/1.10  thf('46', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.89/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.10  thf('47', plain,
% 0.89/1.10      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.89/1.10         (((X32) = (k1_xboole_0))
% 0.89/1.10          | ((X33) = (k1_xboole_0))
% 0.89/1.10          | ((k5_mcart_1 @ X32 @ X33 @ X35 @ X34)
% 0.89/1.10              = (k1_mcart_1 @ (k1_mcart_1 @ X34)))
% 0.89/1.10          | ~ (m1_subset_1 @ X34 @ (k3_zfmisc_1 @ X32 @ X33 @ X35))
% 0.89/1.10          | ((X35) = (k1_xboole_0)))),
% 0.89/1.10      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.89/1.10  thf('48', plain,
% 0.89/1.10      ((((sk_C) = (k1_xboole_0))
% 0.89/1.10        | ((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.89/1.10            = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.89/1.10        | ((sk_B) = (k1_xboole_0))
% 0.89/1.10        | ((sk_A) = (k1_xboole_0)))),
% 0.89/1.10      inference('sup-', [status(thm)], ['46', '47'])).
% 0.89/1.10  thf('49', plain, (((sk_A) != (k1_xboole_0))),
% 0.89/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.10  thf('50', plain, (((sk_B) != (k1_xboole_0))),
% 0.89/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.10  thf('51', plain, (((sk_C) != (k1_xboole_0))),
% 0.89/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.10  thf('52', plain,
% 0.89/1.10      (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.89/1.10         = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 0.89/1.10      inference('simplify_reflect-', [status(thm)], ['48', '49', '50', '51'])).
% 0.89/1.10  thf('53', plain, ((m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)),
% 0.89/1.10      inference('demod', [status(thm)], ['45', '52'])).
% 0.89/1.10  thf('54', plain,
% 0.89/1.10      (![X0 : $i]:
% 0.89/1.10         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.89/1.10          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.89/1.10          | ((sk_D) = (X0))
% 0.89/1.10          | ~ (m1_subset_1 @ X0 @ sk_C))),
% 0.89/1.10      inference('demod', [status(thm)], ['42', '53'])).
% 0.89/1.10  thf('55', plain,
% 0.89/1.10      ((((sk_E) != (sk_E))
% 0.89/1.10        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)
% 0.89/1.10        | ((sk_D) = (k2_mcart_1 @ sk_E))
% 0.89/1.10        | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 0.89/1.10      inference('sup-', [status(thm)], ['17', '54'])).
% 0.89/1.10  thf('56', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.89/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.10  thf(dt_k7_mcart_1, axiom,
% 0.89/1.10    (![A:$i,B:$i,C:$i,D:$i]:
% 0.89/1.10     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.89/1.10       ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ))).
% 0.89/1.10  thf('57', plain,
% 0.89/1.10      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.89/1.10         ((m1_subset_1 @ (k7_mcart_1 @ X19 @ X20 @ X21 @ X22) @ X21)
% 0.89/1.10          | ~ (m1_subset_1 @ X22 @ (k3_zfmisc_1 @ X19 @ X20 @ X21)))),
% 0.89/1.10      inference('cnf', [status(esa)], [dt_k7_mcart_1])).
% 0.89/1.10  thf('58', plain,
% 0.89/1.10      ((m1_subset_1 @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_C)),
% 0.89/1.10      inference('sup-', [status(thm)], ['56', '57'])).
% 0.89/1.10  thf('59', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.89/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.10  thf('60', plain,
% 0.89/1.10      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.89/1.10         (((X32) = (k1_xboole_0))
% 0.89/1.10          | ((X33) = (k1_xboole_0))
% 0.89/1.10          | ((k7_mcart_1 @ X32 @ X33 @ X35 @ X34) = (k2_mcart_1 @ X34))
% 0.89/1.10          | ~ (m1_subset_1 @ X34 @ (k3_zfmisc_1 @ X32 @ X33 @ X35))
% 0.89/1.10          | ((X35) = (k1_xboole_0)))),
% 0.89/1.10      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.89/1.10  thf('61', plain,
% 0.89/1.10      ((((sk_C) = (k1_xboole_0))
% 0.89/1.10        | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))
% 0.89/1.10        | ((sk_B) = (k1_xboole_0))
% 0.89/1.10        | ((sk_A) = (k1_xboole_0)))),
% 0.89/1.10      inference('sup-', [status(thm)], ['59', '60'])).
% 0.89/1.10  thf('62', plain, (((sk_A) != (k1_xboole_0))),
% 0.89/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.10  thf('63', plain, (((sk_B) != (k1_xboole_0))),
% 0.89/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.10  thf('64', plain, (((sk_C) != (k1_xboole_0))),
% 0.89/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.10  thf('65', plain,
% 0.89/1.10      (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))),
% 0.89/1.10      inference('simplify_reflect-', [status(thm)], ['61', '62', '63', '64'])).
% 0.89/1.10  thf('66', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)),
% 0.89/1.10      inference('demod', [status(thm)], ['58', '65'])).
% 0.89/1.10  thf('67', plain,
% 0.89/1.10      ((((sk_E) != (sk_E))
% 0.89/1.10        | ((sk_D) = (k2_mcart_1 @ sk_E))
% 0.89/1.10        | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 0.89/1.10      inference('demod', [status(thm)], ['55', '66'])).
% 0.89/1.10  thf('68', plain,
% 0.89/1.10      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.89/1.10        | ((sk_D) = (k2_mcart_1 @ sk_E)))),
% 0.89/1.10      inference('simplify', [status(thm)], ['67'])).
% 0.89/1.10  thf('69', plain, (((sk_D) != (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E))),
% 0.89/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.10  thf('70', plain,
% 0.89/1.10      (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))),
% 0.89/1.10      inference('simplify_reflect-', [status(thm)], ['61', '62', '63', '64'])).
% 0.89/1.10  thf('71', plain, (((sk_D) != (k2_mcart_1 @ sk_E))),
% 0.89/1.10      inference('demod', [status(thm)], ['69', '70'])).
% 0.89/1.10  thf('72', plain, ((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.89/1.10      inference('simplify_reflect-', [status(thm)], ['68', '71'])).
% 0.89/1.10  thf('73', plain,
% 0.89/1.10      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.89/1.10      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.89/1.10  thf('74', plain, (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))),
% 0.89/1.10      inference('sup-', [status(thm)], ['72', '73'])).
% 0.89/1.10  thf('75', plain,
% 0.89/1.10      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.89/1.10         (((k3_zfmisc_1 @ X28 @ X29 @ X30) != (k1_xboole_0))
% 0.89/1.10          | ((X30) = (k1_xboole_0))
% 0.89/1.10          | ((X29) = (k1_xboole_0))
% 0.89/1.10          | ((X28) = (k1_xboole_0)))),
% 0.89/1.10      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.89/1.10  thf('76', plain,
% 0.89/1.10      ((((k1_xboole_0) != (k1_xboole_0))
% 0.89/1.10        | ((sk_A) = (k1_xboole_0))
% 0.89/1.10        | ((sk_B) = (k1_xboole_0))
% 0.89/1.10        | ((sk_C) = (k1_xboole_0)))),
% 0.89/1.10      inference('sup-', [status(thm)], ['74', '75'])).
% 0.89/1.10  thf('77', plain,
% 0.89/1.10      ((((sk_C) = (k1_xboole_0))
% 0.89/1.10        | ((sk_B) = (k1_xboole_0))
% 0.89/1.10        | ((sk_A) = (k1_xboole_0)))),
% 0.89/1.10      inference('simplify', [status(thm)], ['76'])).
% 0.89/1.10  thf('78', plain, (((sk_A) != (k1_xboole_0))),
% 0.89/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.10  thf('79', plain, (((sk_B) != (k1_xboole_0))),
% 0.89/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.10  thf('80', plain, (((sk_C) != (k1_xboole_0))),
% 0.89/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.10  thf('81', plain, ($false),
% 0.89/1.10      inference('simplify_reflect-', [status(thm)], ['77', '78', '79', '80'])).
% 0.89/1.10  
% 0.89/1.10  % SZS output end Refutation
% 0.89/1.10  
% 0.89/1.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
