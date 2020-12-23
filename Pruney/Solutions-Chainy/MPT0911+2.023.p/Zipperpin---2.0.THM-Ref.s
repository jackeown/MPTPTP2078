%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.V8jpgFAKZU

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:59 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 197 expanded)
%              Number of leaves         :   30 (  70 expanded)
%              Depth                    :   20
%              Number of atoms          : 1147 (3805 expanded)
%              Number of equality atoms :  155 ( 556 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_zfmisc_1 @ X12 @ X13 @ X14 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) @ X14 ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( X30 = k1_xboole_0 )
      | ( X31
        = ( k4_tarski @ ( k1_mcart_1 @ X31 ) @ ( k2_mcart_1 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k2_zfmisc_1 @ X30 @ X32 ) )
      | ( X32 = k1_xboole_0 ) ) ),
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

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('7',plain,(
    ! [X1: $i,X2: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('8',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( sk_E
    = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['9','10','11'])).

thf('13',plain,(
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

thf('14',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X5 )
      | ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('15',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_zfmisc_1 @ X12 @ X13 @ X14 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('17',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X27 ) @ X28 )
      | ~ ( r2_hidden @ X27 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( m1_subset_1 @ X4 @ X5 )
      | ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('21',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( X30 = k1_xboole_0 )
      | ( X31
        = ( k4_tarski @ ( k1_mcart_1 @ X31 ) @ ( k2_mcart_1 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k2_zfmisc_1 @ X30 @ X32 ) )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t24_mcart_1])).

thf('23',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( sk_B = k1_xboole_0 )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_zfmisc_1 @ X12 @ X13 @ X14 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('28',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('29',plain,(
    ! [X1: $i,X2: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X1 )
       != X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X1: $i,X2: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,
    ( ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
    | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( sk_C = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('34',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
    | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('37',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('38',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_mcart_1 @ X9 @ X10 @ X11 )
      = ( k4_tarski @ ( k4_tarski @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X0 )
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k6_mcart_1 @ A @ B @ C @ D ) @ B ) ) )).

thf('41',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( m1_subset_1 @ ( k6_mcart_1 @ X19 @ X20 @ X21 @ X22 ) @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( k3_zfmisc_1 @ X19 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_mcart_1])).

thf('42',plain,(
    m1_subset_1 @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_B ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
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

thf('44',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( X33 = k1_xboole_0 )
      | ( X34 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X33 @ X34 @ X36 @ X35 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k3_zfmisc_1 @ X33 @ X34 @ X36 ) )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('45',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['45','46','47','48'])).

thf('50',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B ),
    inference(demod,[status(thm)],['42','49'])).

thf('51',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ sk_B )
      | ( sk_E
       != ( k3_mcart_1 @ X38 @ X37 @ X39 ) )
      | ( sk_D = X39 )
      | ~ ( m1_subset_1 @ X39 @ sk_C )
      | ~ ( m1_subset_1 @ X38 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_D = X1 )
      | ( sk_E
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ A ) ) )).

thf('55',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( m1_subset_1 @ ( k5_mcart_1 @ X15 @ X16 @ X17 @ X18 ) @ X15 )
      | ~ ( m1_subset_1 @ X18 @ ( k3_zfmisc_1 @ X15 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_mcart_1])).

thf('56',plain,(
    m1_subset_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_A ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( X33 = k1_xboole_0 )
      | ( X34 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X33 @ X34 @ X36 @ X35 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k3_zfmisc_1 @ X33 @ X34 @ X36 ) )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('59',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['59','60','61','62'])).

thf('64',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ),
    inference(demod,[status(thm)],['56','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['53','64'])).

thf('66',plain,
    ( ( sk_E != sk_E )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ) )).

thf('68',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( m1_subset_1 @ ( k7_mcart_1 @ X23 @ X24 @ X25 @ X26 ) @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k3_zfmisc_1 @ X23 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_mcart_1])).

thf('69',plain,(
    m1_subset_1 @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_C ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( X33 = k1_xboole_0 )
      | ( X34 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X33 @ X34 @ X36 @ X35 )
        = ( k2_mcart_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k3_zfmisc_1 @ X33 @ X34 @ X36 ) )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('72',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k2_mcart_1 @ sk_E ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['72','73','74','75'])).

thf('77',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['69','76'])).

thf('78',plain,
    ( ( sk_E != sk_E )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','77'])).

thf('79',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    sk_D
 != ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['72','73','74','75'])).

thf('82',plain,(
    sk_D
 != ( k2_mcart_1 @ sk_E ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['79','82'])).

thf('84',plain,(
    ! [X1: $i,X2: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('85',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['86','87','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.V8jpgFAKZU
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:49:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.60/1.79  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.60/1.79  % Solved by: fo/fo7.sh
% 1.60/1.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.60/1.79  % done 2262 iterations in 1.335s
% 1.60/1.79  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.60/1.79  % SZS output start Refutation
% 1.60/1.79  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 1.60/1.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.60/1.79  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.60/1.79  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 1.60/1.79  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.60/1.79  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 1.60/1.79  thf(sk_D_type, type, sk_D: $i).
% 1.60/1.79  thf(sk_E_type, type, sk_E: $i).
% 1.60/1.79  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 1.60/1.79  thf(sk_C_type, type, sk_C: $i).
% 1.60/1.79  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 1.60/1.79  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.60/1.79  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.60/1.79  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 1.60/1.79  thf(sk_B_type, type, sk_B: $i).
% 1.60/1.79  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.60/1.79  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 1.60/1.79  thf(sk_A_type, type, sk_A: $i).
% 1.60/1.79  thf(t71_mcart_1, conjecture,
% 1.60/1.79    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.60/1.79     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.60/1.79       ( ( ![F:$i]:
% 1.60/1.79           ( ( m1_subset_1 @ F @ A ) =>
% 1.60/1.79             ( ![G:$i]:
% 1.60/1.79               ( ( m1_subset_1 @ G @ B ) =>
% 1.60/1.79                 ( ![H:$i]:
% 1.60/1.79                   ( ( m1_subset_1 @ H @ C ) =>
% 1.60/1.79                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 1.60/1.79                       ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 1.60/1.79         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.60/1.79           ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.60/1.79           ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 1.60/1.79  thf(zf_stmt_0, negated_conjecture,
% 1.60/1.79    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.60/1.79        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.60/1.79          ( ( ![F:$i]:
% 1.60/1.79              ( ( m1_subset_1 @ F @ A ) =>
% 1.60/1.79                ( ![G:$i]:
% 1.60/1.79                  ( ( m1_subset_1 @ G @ B ) =>
% 1.60/1.79                    ( ![H:$i]:
% 1.60/1.79                      ( ( m1_subset_1 @ H @ C ) =>
% 1.60/1.79                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 1.60/1.79                          ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 1.60/1.79            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.60/1.79              ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.60/1.79              ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 1.60/1.79    inference('cnf.neg', [status(esa)], [t71_mcart_1])).
% 1.60/1.79  thf('0', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf(d3_zfmisc_1, axiom,
% 1.60/1.79    (![A:$i,B:$i,C:$i]:
% 1.60/1.79     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 1.60/1.79       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 1.60/1.79  thf('1', plain,
% 1.60/1.79      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.60/1.79         ((k3_zfmisc_1 @ X12 @ X13 @ X14)
% 1.60/1.79           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13) @ X14))),
% 1.60/1.79      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.60/1.79  thf(t24_mcart_1, axiom,
% 1.60/1.79    (![A:$i,B:$i]:
% 1.60/1.79     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.60/1.79          ( ~( ![C:$i]:
% 1.60/1.79               ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 1.60/1.79                 ( ( C ) =
% 1.60/1.79                   ( k4_tarski @ ( k1_mcart_1 @ C ) @ ( k2_mcart_1 @ C ) ) ) ) ) ) ) ))).
% 1.60/1.79  thf('2', plain,
% 1.60/1.79      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.60/1.79         (((X30) = (k1_xboole_0))
% 1.60/1.79          | ((X31) = (k4_tarski @ (k1_mcart_1 @ X31) @ (k2_mcart_1 @ X31)))
% 1.60/1.79          | ~ (m1_subset_1 @ X31 @ (k2_zfmisc_1 @ X30 @ X32))
% 1.60/1.79          | ((X32) = (k1_xboole_0)))),
% 1.60/1.79      inference('cnf', [status(esa)], [t24_mcart_1])).
% 1.60/1.79  thf('3', plain,
% 1.60/1.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.60/1.79         (~ (m1_subset_1 @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.60/1.79          | ((X0) = (k1_xboole_0))
% 1.60/1.79          | ((X3) = (k4_tarski @ (k1_mcart_1 @ X3) @ (k2_mcart_1 @ X3)))
% 1.60/1.79          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0)))),
% 1.60/1.79      inference('sup-', [status(thm)], ['1', '2'])).
% 1.60/1.79  thf('4', plain,
% 1.60/1.79      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 1.60/1.79        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 1.60/1.79        | ((sk_C) = (k1_xboole_0)))),
% 1.60/1.79      inference('sup-', [status(thm)], ['0', '3'])).
% 1.60/1.79  thf('5', plain, (((sk_C) != (k1_xboole_0))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf('6', plain,
% 1.60/1.79      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 1.60/1.79        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 1.60/1.79      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 1.60/1.79  thf(t113_zfmisc_1, axiom,
% 1.60/1.79    (![A:$i,B:$i]:
% 1.60/1.79     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.60/1.79       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.60/1.79  thf('7', plain,
% 1.60/1.79      (![X1 : $i, X2 : $i]:
% 1.60/1.79         (((X1) = (k1_xboole_0))
% 1.60/1.79          | ((X2) = (k1_xboole_0))
% 1.60/1.79          | ((k2_zfmisc_1 @ X2 @ X1) != (k1_xboole_0)))),
% 1.60/1.79      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.60/1.79  thf('8', plain,
% 1.60/1.79      ((((k1_xboole_0) != (k1_xboole_0))
% 1.60/1.79        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 1.60/1.79        | ((sk_A) = (k1_xboole_0))
% 1.60/1.79        | ((sk_B) = (k1_xboole_0)))),
% 1.60/1.79      inference('sup-', [status(thm)], ['6', '7'])).
% 1.60/1.79  thf('9', plain,
% 1.60/1.79      ((((sk_B) = (k1_xboole_0))
% 1.60/1.79        | ((sk_A) = (k1_xboole_0))
% 1.60/1.79        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 1.60/1.79      inference('simplify', [status(thm)], ['8'])).
% 1.60/1.79  thf('10', plain, (((sk_A) != (k1_xboole_0))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf('11', plain, (((sk_B) != (k1_xboole_0))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf('12', plain,
% 1.60/1.79      (((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))),
% 1.60/1.79      inference('simplify_reflect-', [status(thm)], ['9', '10', '11'])).
% 1.60/1.79  thf('13', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf(d2_subset_1, axiom,
% 1.60/1.79    (![A:$i,B:$i]:
% 1.60/1.79     ( ( ( v1_xboole_0 @ A ) =>
% 1.60/1.79         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.60/1.79       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.60/1.79         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.60/1.79  thf('14', plain,
% 1.60/1.79      (![X4 : $i, X5 : $i]:
% 1.60/1.79         (~ (m1_subset_1 @ X4 @ X5)
% 1.60/1.79          | (r2_hidden @ X4 @ X5)
% 1.60/1.79          | (v1_xboole_0 @ X5))),
% 1.60/1.79      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.60/1.79  thf('15', plain,
% 1.60/1.79      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 1.60/1.79        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 1.60/1.79      inference('sup-', [status(thm)], ['13', '14'])).
% 1.60/1.79  thf('16', plain,
% 1.60/1.79      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.60/1.79         ((k3_zfmisc_1 @ X12 @ X13 @ X14)
% 1.60/1.79           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13) @ X14))),
% 1.60/1.79      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.60/1.79  thf(t10_mcart_1, axiom,
% 1.60/1.79    (![A:$i,B:$i,C:$i]:
% 1.60/1.79     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 1.60/1.79       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 1.60/1.79         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 1.60/1.79  thf('17', plain,
% 1.60/1.79      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.60/1.79         ((r2_hidden @ (k1_mcart_1 @ X27) @ X28)
% 1.60/1.79          | ~ (r2_hidden @ X27 @ (k2_zfmisc_1 @ X28 @ X29)))),
% 1.60/1.79      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.60/1.79  thf('18', plain,
% 1.60/1.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.60/1.79         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.60/1.79          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 1.60/1.79      inference('sup-', [status(thm)], ['16', '17'])).
% 1.60/1.79  thf('19', plain,
% 1.60/1.79      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 1.60/1.79        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.60/1.79      inference('sup-', [status(thm)], ['15', '18'])).
% 1.60/1.79  thf('20', plain,
% 1.60/1.79      (![X4 : $i, X5 : $i]:
% 1.60/1.79         (~ (r2_hidden @ X4 @ X5)
% 1.60/1.79          | (m1_subset_1 @ X4 @ X5)
% 1.60/1.79          | (v1_xboole_0 @ X5))),
% 1.60/1.79      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.60/1.79  thf('21', plain,
% 1.60/1.79      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 1.60/1.79        | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 1.60/1.79        | (m1_subset_1 @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.60/1.79      inference('sup-', [status(thm)], ['19', '20'])).
% 1.60/1.79  thf('22', plain,
% 1.60/1.79      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.60/1.79         (((X30) = (k1_xboole_0))
% 1.60/1.79          | ((X31) = (k4_tarski @ (k1_mcart_1 @ X31) @ (k2_mcart_1 @ X31)))
% 1.60/1.79          | ~ (m1_subset_1 @ X31 @ (k2_zfmisc_1 @ X30 @ X32))
% 1.60/1.79          | ((X32) = (k1_xboole_0)))),
% 1.60/1.79      inference('cnf', [status(esa)], [t24_mcart_1])).
% 1.60/1.79  thf('23', plain,
% 1.60/1.79      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 1.60/1.79        | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 1.60/1.79        | ((sk_B) = (k1_xboole_0))
% 1.60/1.79        | ((k1_mcart_1 @ sk_E)
% 1.60/1.79            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 1.60/1.79               (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 1.60/1.79        | ((sk_A) = (k1_xboole_0)))),
% 1.60/1.79      inference('sup-', [status(thm)], ['21', '22'])).
% 1.60/1.79  thf('24', plain, (((sk_A) != (k1_xboole_0))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf('25', plain, (((sk_B) != (k1_xboole_0))),
% 1.60/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.79  thf('26', plain,
% 1.60/1.79      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 1.60/1.79        | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 1.60/1.79        | ((k1_mcart_1 @ sk_E)
% 1.60/1.79            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 1.60/1.79               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 1.60/1.79      inference('simplify_reflect-', [status(thm)], ['23', '24', '25'])).
% 1.60/1.79  thf('27', plain,
% 1.60/1.79      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.60/1.80         ((k3_zfmisc_1 @ X12 @ X13 @ X14)
% 1.60/1.80           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13) @ X14))),
% 1.60/1.80      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.60/1.80  thf(l13_xboole_0, axiom,
% 1.60/1.80    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.60/1.80  thf('28', plain,
% 1.60/1.80      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.60/1.80      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.60/1.80  thf('29', plain,
% 1.60/1.80      (![X1 : $i, X2 : $i]:
% 1.60/1.80         (((X1) = (k1_xboole_0))
% 1.60/1.80          | ((X2) = (k1_xboole_0))
% 1.60/1.80          | ((k2_zfmisc_1 @ X2 @ X1) != (k1_xboole_0)))),
% 1.60/1.80      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.60/1.80  thf('30', plain,
% 1.60/1.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.60/1.80         (((k2_zfmisc_1 @ X2 @ X1) != (X0))
% 1.60/1.80          | ~ (v1_xboole_0 @ X0)
% 1.60/1.80          | ((X2) = (k1_xboole_0))
% 1.60/1.80          | ((X1) = (k1_xboole_0)))),
% 1.60/1.80      inference('sup-', [status(thm)], ['28', '29'])).
% 1.60/1.80  thf('31', plain,
% 1.60/1.80      (![X1 : $i, X2 : $i]:
% 1.60/1.80         (((X1) = (k1_xboole_0))
% 1.60/1.80          | ((X2) = (k1_xboole_0))
% 1.60/1.80          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1)))),
% 1.60/1.80      inference('simplify', [status(thm)], ['30'])).
% 1.60/1.80  thf('32', plain,
% 1.60/1.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.60/1.80         (~ (v1_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.60/1.80          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 1.60/1.80          | ((X0) = (k1_xboole_0)))),
% 1.60/1.80      inference('sup-', [status(thm)], ['27', '31'])).
% 1.60/1.80  thf('33', plain,
% 1.60/1.80      ((((k1_mcart_1 @ sk_E)
% 1.60/1.80          = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 1.60/1.80             (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 1.60/1.80        | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 1.60/1.80        | ((sk_C) = (k1_xboole_0))
% 1.60/1.80        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 1.60/1.80      inference('sup-', [status(thm)], ['26', '32'])).
% 1.60/1.80  thf('34', plain, (((sk_C) != (k1_xboole_0))),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf('35', plain,
% 1.60/1.80      ((((k1_mcart_1 @ sk_E)
% 1.60/1.80          = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 1.60/1.80             (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 1.60/1.80        | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 1.60/1.80        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 1.60/1.80      inference('simplify_reflect-', [status(thm)], ['33', '34'])).
% 1.60/1.80  thf('36', plain,
% 1.60/1.80      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.60/1.80      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.60/1.80  thf('37', plain,
% 1.60/1.80      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 1.60/1.80        | ((k1_mcart_1 @ sk_E)
% 1.60/1.80            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 1.60/1.80               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 1.60/1.80      inference('clc', [status(thm)], ['35', '36'])).
% 1.60/1.80  thf(d3_mcart_1, axiom,
% 1.60/1.80    (![A:$i,B:$i,C:$i]:
% 1.60/1.80     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 1.60/1.80  thf('38', plain,
% 1.60/1.80      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.60/1.80         ((k3_mcart_1 @ X9 @ X10 @ X11)
% 1.60/1.80           = (k4_tarski @ (k4_tarski @ X9 @ X10) @ X11))),
% 1.60/1.80      inference('cnf', [status(esa)], [d3_mcart_1])).
% 1.60/1.80  thf('39', plain,
% 1.60/1.80      (![X0 : $i]:
% 1.60/1.80         (((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 1.60/1.80            (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X0)
% 1.60/1.80            = (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 1.60/1.80          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 1.60/1.80      inference('sup+', [status(thm)], ['37', '38'])).
% 1.60/1.80  thf('40', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf(dt_k6_mcart_1, axiom,
% 1.60/1.80    (![A:$i,B:$i,C:$i,D:$i]:
% 1.60/1.80     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.60/1.80       ( m1_subset_1 @ ( k6_mcart_1 @ A @ B @ C @ D ) @ B ) ))).
% 1.60/1.80  thf('41', plain,
% 1.60/1.80      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.60/1.80         ((m1_subset_1 @ (k6_mcart_1 @ X19 @ X20 @ X21 @ X22) @ X20)
% 1.60/1.80          | ~ (m1_subset_1 @ X22 @ (k3_zfmisc_1 @ X19 @ X20 @ X21)))),
% 1.60/1.80      inference('cnf', [status(esa)], [dt_k6_mcart_1])).
% 1.60/1.80  thf('42', plain,
% 1.60/1.80      ((m1_subset_1 @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_B)),
% 1.60/1.80      inference('sup-', [status(thm)], ['40', '41'])).
% 1.60/1.80  thf('43', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf(t50_mcart_1, axiom,
% 1.60/1.80    (![A:$i,B:$i,C:$i]:
% 1.60/1.80     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.60/1.80          ( ( C ) != ( k1_xboole_0 ) ) & 
% 1.60/1.80          ( ~( ![D:$i]:
% 1.60/1.80               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.60/1.80                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 1.60/1.80                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 1.60/1.80                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 1.60/1.80                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 1.60/1.80                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 1.60/1.80  thf('44', plain,
% 1.60/1.80      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 1.60/1.80         (((X33) = (k1_xboole_0))
% 1.60/1.80          | ((X34) = (k1_xboole_0))
% 1.60/1.80          | ((k6_mcart_1 @ X33 @ X34 @ X36 @ X35)
% 1.60/1.80              = (k2_mcart_1 @ (k1_mcart_1 @ X35)))
% 1.60/1.80          | ~ (m1_subset_1 @ X35 @ (k3_zfmisc_1 @ X33 @ X34 @ X36))
% 1.60/1.80          | ((X36) = (k1_xboole_0)))),
% 1.60/1.80      inference('cnf', [status(esa)], [t50_mcart_1])).
% 1.60/1.80  thf('45', plain,
% 1.60/1.80      ((((sk_C) = (k1_xboole_0))
% 1.60/1.80        | ((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 1.60/1.80            = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 1.60/1.80        | ((sk_B) = (k1_xboole_0))
% 1.60/1.80        | ((sk_A) = (k1_xboole_0)))),
% 1.60/1.80      inference('sup-', [status(thm)], ['43', '44'])).
% 1.60/1.80  thf('46', plain, (((sk_A) != (k1_xboole_0))),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf('47', plain, (((sk_B) != (k1_xboole_0))),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf('48', plain, (((sk_C) != (k1_xboole_0))),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf('49', plain,
% 1.60/1.80      (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 1.60/1.80         = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 1.60/1.80      inference('simplify_reflect-', [status(thm)], ['45', '46', '47', '48'])).
% 1.60/1.80  thf('50', plain, ((m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B)),
% 1.60/1.80      inference('demod', [status(thm)], ['42', '49'])).
% 1.60/1.80  thf('51', plain,
% 1.60/1.80      (![X37 : $i, X38 : $i, X39 : $i]:
% 1.60/1.80         (~ (m1_subset_1 @ X37 @ sk_B)
% 1.60/1.80          | ((sk_E) != (k3_mcart_1 @ X38 @ X37 @ X39))
% 1.60/1.80          | ((sk_D) = (X39))
% 1.60/1.80          | ~ (m1_subset_1 @ X39 @ sk_C)
% 1.60/1.80          | ~ (m1_subset_1 @ X38 @ sk_A))),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf('52', plain,
% 1.60/1.80      (![X0 : $i, X1 : $i]:
% 1.60/1.80         (~ (m1_subset_1 @ X0 @ sk_A)
% 1.60/1.80          | ~ (m1_subset_1 @ X1 @ sk_C)
% 1.60/1.80          | ((sk_D) = (X1))
% 1.60/1.80          | ((sk_E)
% 1.60/1.80              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1)))),
% 1.60/1.80      inference('sup-', [status(thm)], ['50', '51'])).
% 1.60/1.80  thf('53', plain,
% 1.60/1.80      (![X0 : $i]:
% 1.60/1.80         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 1.60/1.80          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 1.60/1.80          | ((sk_D) = (X0))
% 1.60/1.80          | ~ (m1_subset_1 @ X0 @ sk_C)
% 1.60/1.80          | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 1.60/1.80      inference('sup-', [status(thm)], ['39', '52'])).
% 1.60/1.80  thf('54', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf(dt_k5_mcart_1, axiom,
% 1.60/1.80    (![A:$i,B:$i,C:$i,D:$i]:
% 1.60/1.80     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.60/1.80       ( m1_subset_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ A ) ))).
% 1.60/1.80  thf('55', plain,
% 1.60/1.80      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 1.60/1.80         ((m1_subset_1 @ (k5_mcart_1 @ X15 @ X16 @ X17 @ X18) @ X15)
% 1.60/1.80          | ~ (m1_subset_1 @ X18 @ (k3_zfmisc_1 @ X15 @ X16 @ X17)))),
% 1.60/1.80      inference('cnf', [status(esa)], [dt_k5_mcart_1])).
% 1.60/1.80  thf('56', plain,
% 1.60/1.80      ((m1_subset_1 @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_A)),
% 1.60/1.80      inference('sup-', [status(thm)], ['54', '55'])).
% 1.60/1.80  thf('57', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf('58', plain,
% 1.60/1.80      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 1.60/1.80         (((X33) = (k1_xboole_0))
% 1.60/1.80          | ((X34) = (k1_xboole_0))
% 1.60/1.80          | ((k5_mcart_1 @ X33 @ X34 @ X36 @ X35)
% 1.60/1.80              = (k1_mcart_1 @ (k1_mcart_1 @ X35)))
% 1.60/1.80          | ~ (m1_subset_1 @ X35 @ (k3_zfmisc_1 @ X33 @ X34 @ X36))
% 1.60/1.80          | ((X36) = (k1_xboole_0)))),
% 1.60/1.80      inference('cnf', [status(esa)], [t50_mcart_1])).
% 1.60/1.80  thf('59', plain,
% 1.60/1.80      ((((sk_C) = (k1_xboole_0))
% 1.60/1.80        | ((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 1.60/1.80            = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 1.60/1.80        | ((sk_B) = (k1_xboole_0))
% 1.60/1.80        | ((sk_A) = (k1_xboole_0)))),
% 1.60/1.80      inference('sup-', [status(thm)], ['57', '58'])).
% 1.60/1.80  thf('60', plain, (((sk_A) != (k1_xboole_0))),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf('61', plain, (((sk_B) != (k1_xboole_0))),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf('62', plain, (((sk_C) != (k1_xboole_0))),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf('63', plain,
% 1.60/1.80      (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 1.60/1.80         = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 1.60/1.80      inference('simplify_reflect-', [status(thm)], ['59', '60', '61', '62'])).
% 1.60/1.80  thf('64', plain, ((m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)),
% 1.60/1.80      inference('demod', [status(thm)], ['56', '63'])).
% 1.60/1.80  thf('65', plain,
% 1.60/1.80      (![X0 : $i]:
% 1.60/1.80         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 1.60/1.80          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 1.60/1.80          | ((sk_D) = (X0))
% 1.60/1.80          | ~ (m1_subset_1 @ X0 @ sk_C))),
% 1.60/1.80      inference('demod', [status(thm)], ['53', '64'])).
% 1.60/1.80  thf('66', plain,
% 1.60/1.80      ((((sk_E) != (sk_E))
% 1.60/1.80        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)
% 1.60/1.80        | ((sk_D) = (k2_mcart_1 @ sk_E))
% 1.60/1.80        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 1.60/1.80      inference('sup-', [status(thm)], ['12', '65'])).
% 1.60/1.80  thf('67', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf(dt_k7_mcart_1, axiom,
% 1.60/1.80    (![A:$i,B:$i,C:$i,D:$i]:
% 1.60/1.80     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.60/1.80       ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ))).
% 1.60/1.80  thf('68', plain,
% 1.60/1.80      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.60/1.80         ((m1_subset_1 @ (k7_mcart_1 @ X23 @ X24 @ X25 @ X26) @ X25)
% 1.60/1.80          | ~ (m1_subset_1 @ X26 @ (k3_zfmisc_1 @ X23 @ X24 @ X25)))),
% 1.60/1.80      inference('cnf', [status(esa)], [dt_k7_mcart_1])).
% 1.60/1.80  thf('69', plain,
% 1.60/1.80      ((m1_subset_1 @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_C)),
% 1.60/1.80      inference('sup-', [status(thm)], ['67', '68'])).
% 1.60/1.80  thf('70', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf('71', plain,
% 1.60/1.80      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 1.60/1.80         (((X33) = (k1_xboole_0))
% 1.60/1.80          | ((X34) = (k1_xboole_0))
% 1.60/1.80          | ((k7_mcart_1 @ X33 @ X34 @ X36 @ X35) = (k2_mcart_1 @ X35))
% 1.60/1.80          | ~ (m1_subset_1 @ X35 @ (k3_zfmisc_1 @ X33 @ X34 @ X36))
% 1.60/1.80          | ((X36) = (k1_xboole_0)))),
% 1.60/1.80      inference('cnf', [status(esa)], [t50_mcart_1])).
% 1.60/1.80  thf('72', plain,
% 1.60/1.80      ((((sk_C) = (k1_xboole_0))
% 1.60/1.80        | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))
% 1.60/1.80        | ((sk_B) = (k1_xboole_0))
% 1.60/1.80        | ((sk_A) = (k1_xboole_0)))),
% 1.60/1.80      inference('sup-', [status(thm)], ['70', '71'])).
% 1.60/1.80  thf('73', plain, (((sk_A) != (k1_xboole_0))),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf('74', plain, (((sk_B) != (k1_xboole_0))),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf('75', plain, (((sk_C) != (k1_xboole_0))),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf('76', plain,
% 1.60/1.80      (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))),
% 1.60/1.80      inference('simplify_reflect-', [status(thm)], ['72', '73', '74', '75'])).
% 1.60/1.80  thf('77', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)),
% 1.60/1.80      inference('demod', [status(thm)], ['69', '76'])).
% 1.60/1.80  thf('78', plain,
% 1.60/1.80      ((((sk_E) != (sk_E))
% 1.60/1.80        | ((sk_D) = (k2_mcart_1 @ sk_E))
% 1.60/1.80        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 1.60/1.80      inference('demod', [status(thm)], ['66', '77'])).
% 1.60/1.80  thf('79', plain,
% 1.60/1.80      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 1.60/1.80        | ((sk_D) = (k2_mcart_1 @ sk_E)))),
% 1.60/1.80      inference('simplify', [status(thm)], ['78'])).
% 1.60/1.80  thf('80', plain, (((sk_D) != (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E))),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf('81', plain,
% 1.60/1.80      (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))),
% 1.60/1.80      inference('simplify_reflect-', [status(thm)], ['72', '73', '74', '75'])).
% 1.60/1.80  thf('82', plain, (((sk_D) != (k2_mcart_1 @ sk_E))),
% 1.60/1.80      inference('demod', [status(thm)], ['80', '81'])).
% 1.60/1.80  thf('83', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 1.60/1.80      inference('simplify_reflect-', [status(thm)], ['79', '82'])).
% 1.60/1.80  thf('84', plain,
% 1.60/1.80      (![X1 : $i, X2 : $i]:
% 1.60/1.80         (((X1) = (k1_xboole_0))
% 1.60/1.80          | ((X2) = (k1_xboole_0))
% 1.60/1.80          | ((k2_zfmisc_1 @ X2 @ X1) != (k1_xboole_0)))),
% 1.60/1.80      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.60/1.80  thf('85', plain,
% 1.60/1.80      ((((k1_xboole_0) != (k1_xboole_0))
% 1.60/1.80        | ((sk_A) = (k1_xboole_0))
% 1.60/1.80        | ((sk_B) = (k1_xboole_0)))),
% 1.60/1.80      inference('sup-', [status(thm)], ['83', '84'])).
% 1.60/1.80  thf('86', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 1.60/1.80      inference('simplify', [status(thm)], ['85'])).
% 1.60/1.80  thf('87', plain, (((sk_A) != (k1_xboole_0))),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf('88', plain, (((sk_B) != (k1_xboole_0))),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf('89', plain, ($false),
% 1.60/1.80      inference('simplify_reflect-', [status(thm)], ['86', '87', '88'])).
% 1.60/1.80  
% 1.60/1.80  % SZS output end Refutation
% 1.60/1.80  
% 1.60/1.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
