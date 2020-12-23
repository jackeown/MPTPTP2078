%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7JgrP7ttWv

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:50 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 216 expanded)
%              Number of leaves         :   28 (  77 expanded)
%              Depth                    :   15
%              Number of atoms          :  972 (4185 expanded)
%              Number of equality atoms :  126 ( 589 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( D
                = ( k3_mcart_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ ( k6_mcart_1 @ A @ B @ C @ D ) @ ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf('1',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( X28
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X25 @ X26 @ X27 @ X28 ) @ ( k6_mcart_1 @ X25 @ X26 @ X27 @ X28 ) @ ( k7_mcart_1 @ X25 @ X26 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k3_zfmisc_1 @ X25 @ X26 @ X27 ) )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t48_mcart_1])).

thf('2',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_E
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( sk_E
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
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

thf('8',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( X29 = k1_xboole_0 )
      | ( X30 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X29 @ X30 @ X32 @ X31 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k3_zfmisc_1 @ X29 @ X30 @ X32 ) )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('9',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['9','10','11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( X29 = k1_xboole_0 )
      | ( X30 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X29 @ X30 @ X32 @ X31 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k3_zfmisc_1 @ X29 @ X30 @ X32 ) )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('16',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['16','17','18','19'])).

thf('21',plain,
    ( sk_E
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['6','13','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( X29 = k1_xboole_0 )
      | ( X30 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X29 @ X30 @ X32 @ X31 )
        = ( k2_mcart_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k3_zfmisc_1 @ X29 @ X30 @ X32 ) )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('24',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E )
      = ( k2_mcart_1 @ sk_E ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['24','25','26','27'])).

thf('29',plain,
    ( sk_E
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['21','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('31',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('32',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('33',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_zfmisc_1 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('34',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X18 ) @ X19 )
      | ~ ( r2_hidden @ X18 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('37',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('38',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( k1_xboole_0
      = ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X18 ) @ X20 )
      | ~ ( r2_hidden @ X18 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('42',plain,
    ( ( k1_xboole_0
      = ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t35_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) )
    <=> ( ( k3_zfmisc_1 @ A @ B @ C )
       != k1_xboole_0 ) ) )).

thf('43',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k3_zfmisc_1 @ X21 @ X22 @ X23 )
       != k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('44',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_1 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['45','46','47','48'])).

thf('50',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( m1_subset_1 @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('52',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ X5 @ X6 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ sk_B_1 )
      | ( sk_D = X34 )
      | ( sk_E
       != ( k3_mcart_1 @ X34 @ X33 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ sk_C )
      | ~ ( m1_subset_1 @ X34 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_E
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 ) )
      | ( sk_D = X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_E != sk_E )
    | ( sk_D
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['29','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ) )).

thf('58',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k7_mcart_1 @ X14 @ X15 @ X16 @ X17 ) @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k3_zfmisc_1 @ X14 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_mcart_1])).

thf('59',plain,(
    m1_subset_1 @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) @ sk_C ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['24','25','26','27'])).

thf('61',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( k1_xboole_0
      = ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('63',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X18 ) @ X19 )
      | ~ ( r2_hidden @ X18 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('64',plain,
    ( ( k1_xboole_0
      = ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k3_zfmisc_1 @ X21 @ X22 @ X23 )
       != k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('66',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['67','68','69','70'])).

thf('72',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ X5 @ X6 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('73',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( sk_E != sk_E )
    | ( sk_D
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['56','61','73'])).

thf('75',plain,
    ( sk_D
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    sk_D
 != ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['9','10','11','12'])).

thf('78',plain,(
    sk_D
 != ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['75','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7JgrP7ttWv
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:57:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.47/1.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.47/1.64  % Solved by: fo/fo7.sh
% 1.47/1.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.47/1.64  % done 1104 iterations in 1.186s
% 1.47/1.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.47/1.64  % SZS output start Refutation
% 1.47/1.64  thf(sk_D_type, type, sk_D: $i).
% 1.47/1.64  thf(sk_E_type, type, sk_E: $i).
% 1.47/1.64  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 1.47/1.64  thf(sk_C_type, type, sk_C: $i).
% 1.47/1.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.47/1.64  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 1.47/1.64  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 1.47/1.64  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.47/1.64  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 1.47/1.64  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 1.47/1.64  thf(sk_A_type, type, sk_A: $i).
% 1.47/1.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.47/1.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.47/1.64  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.47/1.64  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 1.47/1.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.47/1.64  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 1.47/1.64  thf(t69_mcart_1, conjecture,
% 1.47/1.64    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.47/1.64     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.47/1.64       ( ( ![F:$i]:
% 1.47/1.64           ( ( m1_subset_1 @ F @ A ) =>
% 1.47/1.64             ( ![G:$i]:
% 1.47/1.64               ( ( m1_subset_1 @ G @ B ) =>
% 1.47/1.64                 ( ![H:$i]:
% 1.47/1.64                   ( ( m1_subset_1 @ H @ C ) =>
% 1.47/1.64                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 1.47/1.64                       ( ( D ) = ( F ) ) ) ) ) ) ) ) ) =>
% 1.47/1.64         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.47/1.64           ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.47/1.64           ( ( D ) = ( k5_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 1.47/1.64  thf(zf_stmt_0, negated_conjecture,
% 1.47/1.64    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.47/1.64        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.47/1.64          ( ( ![F:$i]:
% 1.47/1.64              ( ( m1_subset_1 @ F @ A ) =>
% 1.47/1.64                ( ![G:$i]:
% 1.47/1.64                  ( ( m1_subset_1 @ G @ B ) =>
% 1.47/1.64                    ( ![H:$i]:
% 1.47/1.64                      ( ( m1_subset_1 @ H @ C ) =>
% 1.47/1.64                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 1.47/1.64                          ( ( D ) = ( F ) ) ) ) ) ) ) ) ) =>
% 1.47/1.64            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.47/1.64              ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.47/1.64              ( ( D ) = ( k5_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 1.47/1.64    inference('cnf.neg', [status(esa)], [t69_mcart_1])).
% 1.47/1.64  thf('0', plain,
% 1.47/1.64      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 1.47/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.47/1.64  thf(t48_mcart_1, axiom,
% 1.47/1.64    (![A:$i,B:$i,C:$i]:
% 1.47/1.64     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.47/1.64          ( ( C ) != ( k1_xboole_0 ) ) & 
% 1.47/1.64          ( ~( ![D:$i]:
% 1.47/1.64               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.47/1.64                 ( ( D ) =
% 1.47/1.64                   ( k3_mcart_1 @
% 1.47/1.64                     ( k5_mcart_1 @ A @ B @ C @ D ) @ 
% 1.47/1.64                     ( k6_mcart_1 @ A @ B @ C @ D ) @ 
% 1.47/1.64                     ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 1.47/1.64  thf('1', plain,
% 1.47/1.64      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.47/1.64         (((X25) = (k1_xboole_0))
% 1.47/1.64          | ((X26) = (k1_xboole_0))
% 1.47/1.64          | ((X28)
% 1.47/1.64              = (k3_mcart_1 @ (k5_mcart_1 @ X25 @ X26 @ X27 @ X28) @ 
% 1.47/1.64                 (k6_mcart_1 @ X25 @ X26 @ X27 @ X28) @ 
% 1.47/1.64                 (k7_mcart_1 @ X25 @ X26 @ X27 @ X28)))
% 1.47/1.64          | ~ (m1_subset_1 @ X28 @ (k3_zfmisc_1 @ X25 @ X26 @ X27))
% 1.47/1.64          | ((X27) = (k1_xboole_0)))),
% 1.47/1.64      inference('cnf', [status(esa)], [t48_mcart_1])).
% 1.47/1.64  thf('2', plain,
% 1.47/1.64      ((((sk_C) = (k1_xboole_0))
% 1.47/1.64        | ((sk_E)
% 1.47/1.64            = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E) @ 
% 1.47/1.64               (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E) @ 
% 1.47/1.64               (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E)))
% 1.47/1.64        | ((sk_B_1) = (k1_xboole_0))
% 1.47/1.64        | ((sk_A) = (k1_xboole_0)))),
% 1.47/1.64      inference('sup-', [status(thm)], ['0', '1'])).
% 1.47/1.64  thf('3', plain, (((sk_A) != (k1_xboole_0))),
% 1.47/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.47/1.64  thf('4', plain, (((sk_B_1) != (k1_xboole_0))),
% 1.47/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.47/1.64  thf('5', plain, (((sk_C) != (k1_xboole_0))),
% 1.47/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.47/1.64  thf('6', plain,
% 1.47/1.64      (((sk_E)
% 1.47/1.64         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E) @ 
% 1.47/1.64            (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E) @ 
% 1.47/1.64            (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E)))),
% 1.47/1.64      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5'])).
% 1.47/1.64  thf('7', plain,
% 1.47/1.64      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 1.47/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.47/1.64  thf(t50_mcart_1, axiom,
% 1.47/1.64    (![A:$i,B:$i,C:$i]:
% 1.47/1.64     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.47/1.64          ( ( C ) != ( k1_xboole_0 ) ) & 
% 1.47/1.64          ( ~( ![D:$i]:
% 1.47/1.64               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.47/1.64                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 1.47/1.64                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 1.47/1.64                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 1.47/1.64                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 1.47/1.64                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 1.47/1.64  thf('8', plain,
% 1.47/1.64      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 1.47/1.64         (((X29) = (k1_xboole_0))
% 1.47/1.64          | ((X30) = (k1_xboole_0))
% 1.47/1.64          | ((k5_mcart_1 @ X29 @ X30 @ X32 @ X31)
% 1.47/1.64              = (k1_mcart_1 @ (k1_mcart_1 @ X31)))
% 1.47/1.64          | ~ (m1_subset_1 @ X31 @ (k3_zfmisc_1 @ X29 @ X30 @ X32))
% 1.47/1.64          | ((X32) = (k1_xboole_0)))),
% 1.47/1.64      inference('cnf', [status(esa)], [t50_mcart_1])).
% 1.47/1.64  thf('9', plain,
% 1.47/1.64      ((((sk_C) = (k1_xboole_0))
% 1.47/1.64        | ((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E)
% 1.47/1.64            = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 1.47/1.64        | ((sk_B_1) = (k1_xboole_0))
% 1.47/1.64        | ((sk_A) = (k1_xboole_0)))),
% 1.47/1.64      inference('sup-', [status(thm)], ['7', '8'])).
% 1.47/1.64  thf('10', plain, (((sk_A) != (k1_xboole_0))),
% 1.47/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.47/1.64  thf('11', plain, (((sk_B_1) != (k1_xboole_0))),
% 1.47/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.47/1.64  thf('12', plain, (((sk_C) != (k1_xboole_0))),
% 1.47/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.47/1.64  thf('13', plain,
% 1.47/1.64      (((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E)
% 1.47/1.64         = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 1.47/1.64      inference('simplify_reflect-', [status(thm)], ['9', '10', '11', '12'])).
% 1.47/1.64  thf('14', plain,
% 1.47/1.64      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 1.47/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.47/1.64  thf('15', plain,
% 1.47/1.64      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 1.47/1.64         (((X29) = (k1_xboole_0))
% 1.47/1.64          | ((X30) = (k1_xboole_0))
% 1.47/1.64          | ((k6_mcart_1 @ X29 @ X30 @ X32 @ X31)
% 1.47/1.64              = (k2_mcart_1 @ (k1_mcart_1 @ X31)))
% 1.47/1.64          | ~ (m1_subset_1 @ X31 @ (k3_zfmisc_1 @ X29 @ X30 @ X32))
% 1.47/1.64          | ((X32) = (k1_xboole_0)))),
% 1.47/1.64      inference('cnf', [status(esa)], [t50_mcart_1])).
% 1.47/1.64  thf('16', plain,
% 1.47/1.64      ((((sk_C) = (k1_xboole_0))
% 1.47/1.64        | ((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E)
% 1.47/1.64            = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 1.47/1.64        | ((sk_B_1) = (k1_xboole_0))
% 1.47/1.64        | ((sk_A) = (k1_xboole_0)))),
% 1.47/1.64      inference('sup-', [status(thm)], ['14', '15'])).
% 1.47/1.64  thf('17', plain, (((sk_A) != (k1_xboole_0))),
% 1.47/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.47/1.64  thf('18', plain, (((sk_B_1) != (k1_xboole_0))),
% 1.47/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.47/1.64  thf('19', plain, (((sk_C) != (k1_xboole_0))),
% 1.47/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.47/1.64  thf('20', plain,
% 1.47/1.64      (((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E)
% 1.47/1.64         = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 1.47/1.64      inference('simplify_reflect-', [status(thm)], ['16', '17', '18', '19'])).
% 1.47/1.64  thf('21', plain,
% 1.47/1.64      (((sk_E)
% 1.47/1.64         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 1.47/1.64            (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 1.47/1.64            (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E)))),
% 1.47/1.64      inference('demod', [status(thm)], ['6', '13', '20'])).
% 1.47/1.64  thf('22', plain,
% 1.47/1.64      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 1.47/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.47/1.64  thf('23', plain,
% 1.47/1.64      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 1.47/1.64         (((X29) = (k1_xboole_0))
% 1.47/1.64          | ((X30) = (k1_xboole_0))
% 1.47/1.64          | ((k7_mcart_1 @ X29 @ X30 @ X32 @ X31) = (k2_mcart_1 @ X31))
% 1.47/1.64          | ~ (m1_subset_1 @ X31 @ (k3_zfmisc_1 @ X29 @ X30 @ X32))
% 1.47/1.64          | ((X32) = (k1_xboole_0)))),
% 1.47/1.64      inference('cnf', [status(esa)], [t50_mcart_1])).
% 1.47/1.64  thf('24', plain,
% 1.47/1.64      ((((sk_C) = (k1_xboole_0))
% 1.47/1.64        | ((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))
% 1.47/1.64        | ((sk_B_1) = (k1_xboole_0))
% 1.47/1.64        | ((sk_A) = (k1_xboole_0)))),
% 1.47/1.64      inference('sup-', [status(thm)], ['22', '23'])).
% 1.47/1.64  thf('25', plain, (((sk_A) != (k1_xboole_0))),
% 1.47/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.47/1.64  thf('26', plain, (((sk_B_1) != (k1_xboole_0))),
% 1.47/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.47/1.64  thf('27', plain, (((sk_C) != (k1_xboole_0))),
% 1.47/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.47/1.64  thf('28', plain,
% 1.47/1.64      (((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))),
% 1.47/1.64      inference('simplify_reflect-', [status(thm)], ['24', '25', '26', '27'])).
% 1.47/1.64  thf('29', plain,
% 1.47/1.64      (((sk_E)
% 1.47/1.64         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 1.47/1.64            (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ (k2_mcart_1 @ sk_E)))),
% 1.47/1.64      inference('demod', [status(thm)], ['21', '28'])).
% 1.47/1.64  thf('30', plain,
% 1.47/1.64      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 1.47/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.47/1.64  thf(d2_subset_1, axiom,
% 1.47/1.64    (![A:$i,B:$i]:
% 1.47/1.64     ( ( ( v1_xboole_0 @ A ) =>
% 1.47/1.64         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.47/1.64       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.47/1.64         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.47/1.64  thf('31', plain,
% 1.47/1.64      (![X5 : $i, X6 : $i]:
% 1.47/1.64         (~ (m1_subset_1 @ X5 @ X6)
% 1.47/1.64          | (r2_hidden @ X5 @ X6)
% 1.47/1.64          | (v1_xboole_0 @ X6))),
% 1.47/1.64      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.47/1.64  thf('32', plain,
% 1.47/1.64      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))
% 1.47/1.64        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C)))),
% 1.47/1.64      inference('sup-', [status(thm)], ['30', '31'])).
% 1.47/1.64  thf(d3_zfmisc_1, axiom,
% 1.47/1.64    (![A:$i,B:$i,C:$i]:
% 1.47/1.64     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 1.47/1.64       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 1.47/1.64  thf('33', plain,
% 1.47/1.64      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.47/1.64         ((k3_zfmisc_1 @ X11 @ X12 @ X13)
% 1.47/1.64           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12) @ X13))),
% 1.47/1.64      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.47/1.64  thf(t10_mcart_1, axiom,
% 1.47/1.64    (![A:$i,B:$i,C:$i]:
% 1.47/1.64     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 1.47/1.64       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 1.47/1.64         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 1.47/1.64  thf('34', plain,
% 1.47/1.64      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.47/1.64         ((r2_hidden @ (k1_mcart_1 @ X18) @ X19)
% 1.47/1.64          | ~ (r2_hidden @ X18 @ (k2_zfmisc_1 @ X19 @ X20)))),
% 1.47/1.64      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.47/1.64  thf('35', plain,
% 1.47/1.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.47/1.64         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.47/1.64          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 1.47/1.64      inference('sup-', [status(thm)], ['33', '34'])).
% 1.47/1.64  thf('36', plain,
% 1.47/1.64      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))
% 1.47/1.64        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.47/1.64      inference('sup-', [status(thm)], ['32', '35'])).
% 1.47/1.64  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.47/1.64  thf('37', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.47/1.64      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.47/1.64  thf(t8_boole, axiom,
% 1.47/1.64    (![A:$i,B:$i]:
% 1.47/1.64     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 1.47/1.64  thf('38', plain,
% 1.47/1.64      (![X3 : $i, X4 : $i]:
% 1.47/1.64         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 1.47/1.64      inference('cnf', [status(esa)], [t8_boole])).
% 1.47/1.64  thf('39', plain,
% 1.47/1.64      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.47/1.64      inference('sup-', [status(thm)], ['37', '38'])).
% 1.47/1.64  thf('40', plain,
% 1.47/1.64      (((r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 1.47/1.64        | ((k1_xboole_0) = (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C)))),
% 1.47/1.64      inference('sup-', [status(thm)], ['36', '39'])).
% 1.47/1.64  thf('41', plain,
% 1.47/1.64      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.47/1.64         ((r2_hidden @ (k2_mcart_1 @ X18) @ X20)
% 1.47/1.64          | ~ (r2_hidden @ X18 @ (k2_zfmisc_1 @ X19 @ X20)))),
% 1.47/1.64      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.47/1.64  thf('42', plain,
% 1.47/1.64      ((((k1_xboole_0) = (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))
% 1.47/1.64        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_1))),
% 1.47/1.64      inference('sup-', [status(thm)], ['40', '41'])).
% 1.47/1.64  thf(t35_mcart_1, axiom,
% 1.47/1.64    (![A:$i,B:$i,C:$i]:
% 1.47/1.64     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.47/1.64         ( ( C ) != ( k1_xboole_0 ) ) ) <=>
% 1.47/1.64       ( ( k3_zfmisc_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) ))).
% 1.47/1.64  thf('43', plain,
% 1.47/1.64      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.47/1.64         (((k3_zfmisc_1 @ X21 @ X22 @ X23) != (k1_xboole_0))
% 1.47/1.64          | ((X23) = (k1_xboole_0))
% 1.47/1.64          | ((X22) = (k1_xboole_0))
% 1.47/1.64          | ((X21) = (k1_xboole_0)))),
% 1.47/1.64      inference('cnf', [status(esa)], [t35_mcart_1])).
% 1.47/1.64  thf('44', plain,
% 1.47/1.64      ((((k1_xboole_0) != (k1_xboole_0))
% 1.47/1.64        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_1)
% 1.47/1.64        | ((sk_A) = (k1_xboole_0))
% 1.47/1.64        | ((sk_B_1) = (k1_xboole_0))
% 1.47/1.64        | ((sk_C) = (k1_xboole_0)))),
% 1.47/1.64      inference('sup-', [status(thm)], ['42', '43'])).
% 1.47/1.64  thf('45', plain,
% 1.47/1.64      ((((sk_C) = (k1_xboole_0))
% 1.47/1.64        | ((sk_B_1) = (k1_xboole_0))
% 1.47/1.64        | ((sk_A) = (k1_xboole_0))
% 1.47/1.64        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_1))),
% 1.47/1.64      inference('simplify', [status(thm)], ['44'])).
% 1.47/1.64  thf('46', plain, (((sk_A) != (k1_xboole_0))),
% 1.47/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.47/1.64  thf('47', plain, (((sk_B_1) != (k1_xboole_0))),
% 1.47/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.47/1.64  thf('48', plain, (((sk_C) != (k1_xboole_0))),
% 1.47/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.47/1.64  thf('49', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_1)),
% 1.47/1.64      inference('simplify_reflect-', [status(thm)], ['45', '46', '47', '48'])).
% 1.47/1.64  thf('50', plain,
% 1.47/1.64      (![X5 : $i, X6 : $i]:
% 1.47/1.64         (~ (r2_hidden @ X5 @ X6)
% 1.47/1.64          | (m1_subset_1 @ X5 @ X6)
% 1.47/1.64          | (v1_xboole_0 @ X6))),
% 1.47/1.64      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.47/1.64  thf(d1_xboole_0, axiom,
% 1.47/1.64    (![A:$i]:
% 1.47/1.64     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.47/1.64  thf('51', plain,
% 1.47/1.64      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.47/1.64      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.47/1.64  thf('52', plain,
% 1.47/1.64      (![X5 : $i, X6 : $i]: ((m1_subset_1 @ X5 @ X6) | ~ (r2_hidden @ X5 @ X6))),
% 1.47/1.64      inference('clc', [status(thm)], ['50', '51'])).
% 1.47/1.64  thf('53', plain,
% 1.47/1.64      ((m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_1)),
% 1.47/1.64      inference('sup-', [status(thm)], ['49', '52'])).
% 1.47/1.64  thf('54', plain,
% 1.47/1.64      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.47/1.64         (~ (m1_subset_1 @ X33 @ sk_B_1)
% 1.47/1.64          | ((sk_D) = (X34))
% 1.47/1.64          | ((sk_E) != (k3_mcart_1 @ X34 @ X33 @ X35))
% 1.47/1.64          | ~ (m1_subset_1 @ X35 @ sk_C)
% 1.47/1.64          | ~ (m1_subset_1 @ X34 @ sk_A))),
% 1.47/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.47/1.64  thf('55', plain,
% 1.47/1.64      (![X0 : $i, X1 : $i]:
% 1.47/1.64         (~ (m1_subset_1 @ X0 @ sk_A)
% 1.47/1.64          | ~ (m1_subset_1 @ X1 @ sk_C)
% 1.47/1.64          | ((sk_E)
% 1.47/1.64              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1))
% 1.47/1.64          | ((sk_D) = (X0)))),
% 1.47/1.64      inference('sup-', [status(thm)], ['53', '54'])).
% 1.47/1.64  thf('56', plain,
% 1.47/1.64      ((((sk_E) != (sk_E))
% 1.47/1.64        | ((sk_D) = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 1.47/1.64        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)
% 1.47/1.64        | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 1.47/1.64      inference('sup-', [status(thm)], ['29', '55'])).
% 1.47/1.64  thf('57', plain,
% 1.47/1.64      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 1.47/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.47/1.64  thf(dt_k7_mcart_1, axiom,
% 1.47/1.64    (![A:$i,B:$i,C:$i,D:$i]:
% 1.47/1.64     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.47/1.64       ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ))).
% 1.47/1.64  thf('58', plain,
% 1.47/1.64      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 1.47/1.64         ((m1_subset_1 @ (k7_mcart_1 @ X14 @ X15 @ X16 @ X17) @ X16)
% 1.47/1.64          | ~ (m1_subset_1 @ X17 @ (k3_zfmisc_1 @ X14 @ X15 @ X16)))),
% 1.47/1.64      inference('cnf', [status(esa)], [dt_k7_mcart_1])).
% 1.47/1.64  thf('59', plain,
% 1.47/1.64      ((m1_subset_1 @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E) @ sk_C)),
% 1.47/1.64      inference('sup-', [status(thm)], ['57', '58'])).
% 1.47/1.64  thf('60', plain,
% 1.47/1.64      (((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))),
% 1.47/1.64      inference('simplify_reflect-', [status(thm)], ['24', '25', '26', '27'])).
% 1.47/1.64  thf('61', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)),
% 1.47/1.64      inference('demod', [status(thm)], ['59', '60'])).
% 1.47/1.64  thf('62', plain,
% 1.47/1.64      (((r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 1.47/1.64        | ((k1_xboole_0) = (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C)))),
% 1.47/1.64      inference('sup-', [status(thm)], ['36', '39'])).
% 1.47/1.64  thf('63', plain,
% 1.47/1.64      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.47/1.64         ((r2_hidden @ (k1_mcart_1 @ X18) @ X19)
% 1.47/1.64          | ~ (r2_hidden @ X18 @ (k2_zfmisc_1 @ X19 @ X20)))),
% 1.47/1.64      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.47/1.64  thf('64', plain,
% 1.47/1.64      ((((k1_xboole_0) = (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))
% 1.47/1.64        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 1.47/1.64      inference('sup-', [status(thm)], ['62', '63'])).
% 1.47/1.64  thf('65', plain,
% 1.47/1.64      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.47/1.64         (((k3_zfmisc_1 @ X21 @ X22 @ X23) != (k1_xboole_0))
% 1.47/1.64          | ((X23) = (k1_xboole_0))
% 1.47/1.64          | ((X22) = (k1_xboole_0))
% 1.47/1.64          | ((X21) = (k1_xboole_0)))),
% 1.47/1.64      inference('cnf', [status(esa)], [t35_mcart_1])).
% 1.47/1.64  thf('66', plain,
% 1.47/1.64      ((((k1_xboole_0) != (k1_xboole_0))
% 1.47/1.64        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 1.47/1.64        | ((sk_A) = (k1_xboole_0))
% 1.47/1.64        | ((sk_B_1) = (k1_xboole_0))
% 1.47/1.64        | ((sk_C) = (k1_xboole_0)))),
% 1.47/1.64      inference('sup-', [status(thm)], ['64', '65'])).
% 1.47/1.64  thf('67', plain,
% 1.47/1.64      ((((sk_C) = (k1_xboole_0))
% 1.47/1.64        | ((sk_B_1) = (k1_xboole_0))
% 1.47/1.64        | ((sk_A) = (k1_xboole_0))
% 1.47/1.64        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 1.47/1.64      inference('simplify', [status(thm)], ['66'])).
% 1.47/1.64  thf('68', plain, (((sk_A) != (k1_xboole_0))),
% 1.47/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.47/1.64  thf('69', plain, (((sk_B_1) != (k1_xboole_0))),
% 1.47/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.47/1.64  thf('70', plain, (((sk_C) != (k1_xboole_0))),
% 1.47/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.47/1.64  thf('71', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)),
% 1.47/1.64      inference('simplify_reflect-', [status(thm)], ['67', '68', '69', '70'])).
% 1.47/1.64  thf('72', plain,
% 1.47/1.64      (![X5 : $i, X6 : $i]: ((m1_subset_1 @ X5 @ X6) | ~ (r2_hidden @ X5 @ X6))),
% 1.47/1.64      inference('clc', [status(thm)], ['50', '51'])).
% 1.47/1.64  thf('73', plain, ((m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)),
% 1.47/1.64      inference('sup-', [status(thm)], ['71', '72'])).
% 1.47/1.64  thf('74', plain,
% 1.47/1.64      ((((sk_E) != (sk_E)) | ((sk_D) = (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 1.47/1.64      inference('demod', [status(thm)], ['56', '61', '73'])).
% 1.47/1.64  thf('75', plain, (((sk_D) = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 1.47/1.64      inference('simplify', [status(thm)], ['74'])).
% 1.47/1.64  thf('76', plain, (((sk_D) != (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))),
% 1.47/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.47/1.64  thf('77', plain,
% 1.47/1.64      (((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E)
% 1.47/1.64         = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 1.47/1.64      inference('simplify_reflect-', [status(thm)], ['9', '10', '11', '12'])).
% 1.47/1.64  thf('78', plain, (((sk_D) != (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 1.47/1.64      inference('demod', [status(thm)], ['76', '77'])).
% 1.47/1.64  thf('79', plain, ($false),
% 1.47/1.64      inference('simplify_reflect-', [status(thm)], ['75', '78'])).
% 1.47/1.64  
% 1.47/1.64  % SZS output end Refutation
% 1.47/1.64  
% 1.47/1.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
