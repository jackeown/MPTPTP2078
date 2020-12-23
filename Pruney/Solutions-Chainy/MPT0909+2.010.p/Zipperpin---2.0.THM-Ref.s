%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.S1Ld69PXLS

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:51 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 224 expanded)
%              Number of leaves         :   32 (  81 expanded)
%              Depth                    :   21
%              Number of atoms          : 1109 (3583 expanded)
%              Number of equality atoms :  142 ( 484 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ X5 ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ( X21
        = ( k4_tarski @ ( k1_mcart_1 @ X21 ) @ ( k2_mcart_1 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X22 )
      | ~ ( r2_hidden @ X21 @ X22 ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_zfmisc_1 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ),
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

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('9',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
    | ( k1_xboole_0
      = ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf(t35_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) )
    <=> ( ( k3_zfmisc_1 @ A @ B @ C )
       != k1_xboole_0 ) ) )).

thf('13',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k3_zfmisc_1 @ X23 @ X24 @ X25 )
       != k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('14',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( sk_E
    = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['15','16','17','18'])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('21',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_zfmisc_1 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('22',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X18 ) @ X19 )
      | ~ ( r2_hidden @ X18 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X21
        = ( k4_tarski @ ( k1_mcart_1 @ X21 ) @ ( k2_mcart_1 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X22 )
      | ~ ( r2_hidden @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('26',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X6: $i,X7: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('28',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('29',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_mcart_1 @ X8 @ X9 @ X10 )
      = ( k4_tarski @ ( k4_tarski @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X0 )
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('32',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X18 ) @ X20 )
      | ~ ( r2_hidden @ X18 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('35',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B )
    | ( k1_xboole_0
      = ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k3_zfmisc_1 @ X23 @ X24 @ X25 )
       != k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('37',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['38','39','40','41'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('43',plain,(
    ! [X2: $i,X3: $i] :
      ( ( m1_subset_1 @ X2 @ X3 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('44',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ sk_B )
      | ( sk_D = X32 )
      | ( sk_E
       != ( k3_mcart_1 @ X32 @ X31 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ sk_C )
      | ~ ( m1_subset_1 @ X32 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_E
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 ) )
      | ( sk_D = X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
      | ( sk_D
        = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','46'])).

thf('48',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('49',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X18 ) @ X19 )
      | ~ ( r2_hidden @ X18 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('50',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('52',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
    | ( k1_xboole_0
      = ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k3_zfmisc_1 @ X23 @ X24 @ X25 )
       != k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('54',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['55','56','57','58'])).

thf('60',plain,(
    ! [X2: $i,X3: $i] :
      ( ( m1_subset_1 @ X2 @ X3 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('61',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
      | ( sk_D
        = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['47','61'])).

thf('63',plain,(
    sk_D
 != ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
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

thf('65',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( X27 = k1_xboole_0 )
      | ( X28 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X27 @ X28 @ X30 @ X29 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k3_zfmisc_1 @ X27 @ X28 @ X30 ) )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('66',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['66','67','68','69'])).

thf('71',plain,(
    sk_D
 != ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['63','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['62','71'])).

thf('73',plain,
    ( ( sk_E != sk_E )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ) )).

thf('75',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k7_mcart_1 @ X14 @ X15 @ X16 @ X17 ) @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k3_zfmisc_1 @ X14 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_mcart_1])).

thf('76',plain,(
    m1_subset_1 @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_C ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( X27 = k1_xboole_0 )
      | ( X28 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X27 @ X28 @ X30 @ X29 )
        = ( k2_mcart_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k3_zfmisc_1 @ X27 @ X28 @ X30 ) )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('79',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k2_mcart_1 @ sk_E ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['79','80','81','82'])).

thf('84',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['76','83'])).

thf('85',plain,
    ( ( sk_E != sk_E )
    | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['73','84'])).

thf('86',plain,(
    v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('88',plain,
    ( k1_xboole_0
    = ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k3_zfmisc_1 @ X23 @ X24 @ X25 )
       != k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('90',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['91','92','93','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.S1Ld69PXLS
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:40:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.69/0.90  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.69/0.90  % Solved by: fo/fo7.sh
% 0.69/0.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.90  % done 1009 iterations in 0.443s
% 0.69/0.90  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.69/0.90  % SZS output start Refutation
% 0.69/0.90  thf(sk_D_type, type, sk_D: $i).
% 0.69/0.90  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.69/0.90  thf(sk_E_type, type, sk_E: $i).
% 0.69/0.90  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.69/0.90  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.69/0.90  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.69/0.90  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.69/0.90  thf(sk_C_type, type, sk_C: $i).
% 0.69/0.90  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.69/0.90  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.69/0.90  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.69/0.90  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.69/0.90  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.90  thf(sk_B_type, type, sk_B: $i).
% 0.69/0.90  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.69/0.90  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.69/0.90  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.69/0.90  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.69/0.90  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.69/0.90  thf(t69_mcart_1, conjecture,
% 0.69/0.90    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.69/0.90     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.69/0.90       ( ( ![F:$i]:
% 0.69/0.90           ( ( m1_subset_1 @ F @ A ) =>
% 0.69/0.90             ( ![G:$i]:
% 0.69/0.90               ( ( m1_subset_1 @ G @ B ) =>
% 0.69/0.90                 ( ![H:$i]:
% 0.69/0.90                   ( ( m1_subset_1 @ H @ C ) =>
% 0.69/0.90                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.69/0.90                       ( ( D ) = ( F ) ) ) ) ) ) ) ) ) =>
% 0.69/0.90         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.69/0.90           ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.69/0.90           ( ( D ) = ( k5_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 0.69/0.90  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.90    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.69/0.90        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.69/0.90          ( ( ![F:$i]:
% 0.69/0.90              ( ( m1_subset_1 @ F @ A ) =>
% 0.69/0.90                ( ![G:$i]:
% 0.69/0.90                  ( ( m1_subset_1 @ G @ B ) =>
% 0.69/0.90                    ( ![H:$i]:
% 0.69/0.90                      ( ( m1_subset_1 @ H @ C ) =>
% 0.69/0.90                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.69/0.90                          ( ( D ) = ( F ) ) ) ) ) ) ) ) ) =>
% 0.69/0.90            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.69/0.90              ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.69/0.90              ( ( D ) = ( k5_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 0.69/0.90    inference('cnf.neg', [status(esa)], [t69_mcart_1])).
% 0.69/0.90  thf('0', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf(t2_subset, axiom,
% 0.69/0.90    (![A:$i,B:$i]:
% 0.69/0.90     ( ( m1_subset_1 @ A @ B ) =>
% 0.69/0.90       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.69/0.90  thf('1', plain,
% 0.69/0.90      (![X4 : $i, X5 : $i]:
% 0.69/0.90         ((r2_hidden @ X4 @ X5)
% 0.69/0.90          | (v1_xboole_0 @ X5)
% 0.69/0.90          | ~ (m1_subset_1 @ X4 @ X5))),
% 0.69/0.90      inference('cnf', [status(esa)], [t2_subset])).
% 0.69/0.90  thf('2', plain,
% 0.69/0.90      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.69/0.90        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['0', '1'])).
% 0.69/0.90  thf(t23_mcart_1, axiom,
% 0.69/0.90    (![A:$i,B:$i]:
% 0.69/0.90     ( ( v1_relat_1 @ B ) =>
% 0.69/0.90       ( ( r2_hidden @ A @ B ) =>
% 0.69/0.90         ( ( A ) = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ))).
% 0.69/0.90  thf('3', plain,
% 0.69/0.90      (![X21 : $i, X22 : $i]:
% 0.69/0.90         (((X21) = (k4_tarski @ (k1_mcart_1 @ X21) @ (k2_mcart_1 @ X21)))
% 0.69/0.90          | ~ (v1_relat_1 @ X22)
% 0.69/0.90          | ~ (r2_hidden @ X21 @ X22))),
% 0.69/0.90      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.69/0.90  thf('4', plain,
% 0.69/0.90      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.69/0.90        | ~ (v1_relat_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.69/0.90        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.69/0.90      inference('sup-', [status(thm)], ['2', '3'])).
% 0.69/0.90  thf(d3_zfmisc_1, axiom,
% 0.69/0.90    (![A:$i,B:$i,C:$i]:
% 0.69/0.90     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.69/0.90       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.69/0.90  thf('5', plain,
% 0.69/0.90      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.69/0.90         ((k3_zfmisc_1 @ X11 @ X12 @ X13)
% 0.69/0.90           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12) @ X13))),
% 0.69/0.90      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.69/0.90  thf(fc6_relat_1, axiom,
% 0.69/0.90    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.69/0.90  thf('6', plain,
% 0.69/0.90      (![X6 : $i, X7 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X6 @ X7))),
% 0.69/0.90      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.69/0.90  thf('7', plain,
% 0.69/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.90         (v1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))),
% 0.69/0.90      inference('sup+', [status(thm)], ['5', '6'])).
% 0.69/0.90  thf('8', plain,
% 0.69/0.90      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.69/0.90        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.69/0.90      inference('demod', [status(thm)], ['4', '7'])).
% 0.69/0.90  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.69/0.90  thf('9', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.69/0.90      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.69/0.90  thf(t8_boole, axiom,
% 0.69/0.90    (![A:$i,B:$i]:
% 0.69/0.90     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.69/0.90  thf('10', plain,
% 0.69/0.90      (![X0 : $i, X1 : $i]:
% 0.69/0.90         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 0.69/0.90      inference('cnf', [status(esa)], [t8_boole])).
% 0.69/0.90  thf('11', plain,
% 0.69/0.90      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.69/0.90      inference('sup-', [status(thm)], ['9', '10'])).
% 0.69/0.90  thf('12', plain,
% 0.69/0.90      ((((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.69/0.90        | ((k1_xboole_0) = (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['8', '11'])).
% 0.69/0.90  thf(t35_mcart_1, axiom,
% 0.69/0.90    (![A:$i,B:$i,C:$i]:
% 0.69/0.90     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.69/0.90         ( ( C ) != ( k1_xboole_0 ) ) ) <=>
% 0.69/0.90       ( ( k3_zfmisc_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) ))).
% 0.69/0.90  thf('13', plain,
% 0.69/0.90      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.69/0.90         (((k3_zfmisc_1 @ X23 @ X24 @ X25) != (k1_xboole_0))
% 0.69/0.90          | ((X25) = (k1_xboole_0))
% 0.69/0.90          | ((X24) = (k1_xboole_0))
% 0.69/0.90          | ((X23) = (k1_xboole_0)))),
% 0.69/0.90      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.69/0.90  thf('14', plain,
% 0.69/0.90      ((((k1_xboole_0) != (k1_xboole_0))
% 0.69/0.90        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.69/0.90        | ((sk_A) = (k1_xboole_0))
% 0.69/0.90        | ((sk_B) = (k1_xboole_0))
% 0.69/0.90        | ((sk_C) = (k1_xboole_0)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['12', '13'])).
% 0.69/0.90  thf('15', plain,
% 0.69/0.90      ((((sk_C) = (k1_xboole_0))
% 0.69/0.90        | ((sk_B) = (k1_xboole_0))
% 0.69/0.90        | ((sk_A) = (k1_xboole_0))
% 0.69/0.90        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.69/0.90      inference('simplify', [status(thm)], ['14'])).
% 0.69/0.90  thf('16', plain, (((sk_A) != (k1_xboole_0))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('17', plain, (((sk_B) != (k1_xboole_0))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('18', plain, (((sk_C) != (k1_xboole_0))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('19', plain,
% 0.69/0.90      (((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))),
% 0.69/0.90      inference('simplify_reflect-', [status(thm)], ['15', '16', '17', '18'])).
% 0.69/0.90  thf('20', plain,
% 0.69/0.90      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.69/0.90        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['0', '1'])).
% 0.69/0.90  thf('21', plain,
% 0.69/0.90      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.69/0.90         ((k3_zfmisc_1 @ X11 @ X12 @ X13)
% 0.69/0.90           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12) @ X13))),
% 0.69/0.90      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.69/0.90  thf(t10_mcart_1, axiom,
% 0.69/0.90    (![A:$i,B:$i,C:$i]:
% 0.69/0.90     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.69/0.90       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.69/0.90         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.69/0.90  thf('22', plain,
% 0.69/0.90      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.69/0.90         ((r2_hidden @ (k1_mcart_1 @ X18) @ X19)
% 0.69/0.90          | ~ (r2_hidden @ X18 @ (k2_zfmisc_1 @ X19 @ X20)))),
% 0.69/0.90      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.69/0.90  thf('23', plain,
% 0.69/0.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.69/0.90         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.69/0.90          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['21', '22'])).
% 0.69/0.90  thf('24', plain,
% 0.69/0.90      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.69/0.90        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['20', '23'])).
% 0.69/0.90  thf('25', plain,
% 0.69/0.90      (![X21 : $i, X22 : $i]:
% 0.69/0.90         (((X21) = (k4_tarski @ (k1_mcart_1 @ X21) @ (k2_mcart_1 @ X21)))
% 0.69/0.90          | ~ (v1_relat_1 @ X22)
% 0.69/0.90          | ~ (r2_hidden @ X21 @ X22))),
% 0.69/0.90      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.69/0.90  thf('26', plain,
% 0.69/0.90      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.69/0.90        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.69/0.90        | ((k1_mcart_1 @ sk_E)
% 0.69/0.90            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.69/0.90               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 0.69/0.90      inference('sup-', [status(thm)], ['24', '25'])).
% 0.69/0.90  thf('27', plain,
% 0.69/0.90      (![X6 : $i, X7 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X6 @ X7))),
% 0.69/0.90      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.69/0.90  thf('28', plain,
% 0.69/0.90      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.69/0.90        | ((k1_mcart_1 @ sk_E)
% 0.69/0.90            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.69/0.90               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 0.69/0.90      inference('demod', [status(thm)], ['26', '27'])).
% 0.69/0.90  thf(d3_mcart_1, axiom,
% 0.69/0.90    (![A:$i,B:$i,C:$i]:
% 0.69/0.90     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.69/0.90  thf('29', plain,
% 0.69/0.90      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.69/0.90         ((k3_mcart_1 @ X8 @ X9 @ X10)
% 0.69/0.90           = (k4_tarski @ (k4_tarski @ X8 @ X9) @ X10))),
% 0.69/0.90      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.69/0.90  thf('30', plain,
% 0.69/0.90      (![X0 : $i]:
% 0.69/0.90         (((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.69/0.90            (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X0)
% 0.69/0.90            = (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.69/0.90          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 0.69/0.90      inference('sup+', [status(thm)], ['28', '29'])).
% 0.69/0.90  thf('31', plain,
% 0.69/0.90      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.69/0.90        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['20', '23'])).
% 0.69/0.90  thf('32', plain,
% 0.69/0.90      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.69/0.90         ((r2_hidden @ (k2_mcart_1 @ X18) @ X20)
% 0.69/0.90          | ~ (r2_hidden @ X18 @ (k2_zfmisc_1 @ X19 @ X20)))),
% 0.69/0.90      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.69/0.90  thf('33', plain,
% 0.69/0.90      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.69/0.90        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B))),
% 0.69/0.90      inference('sup-', [status(thm)], ['31', '32'])).
% 0.69/0.90  thf('34', plain,
% 0.69/0.90      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.69/0.90      inference('sup-', [status(thm)], ['9', '10'])).
% 0.69/0.90  thf('35', plain,
% 0.69/0.90      (((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B)
% 0.69/0.90        | ((k1_xboole_0) = (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['33', '34'])).
% 0.69/0.90  thf('36', plain,
% 0.69/0.90      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.69/0.90         (((k3_zfmisc_1 @ X23 @ X24 @ X25) != (k1_xboole_0))
% 0.69/0.90          | ((X25) = (k1_xboole_0))
% 0.69/0.90          | ((X24) = (k1_xboole_0))
% 0.69/0.90          | ((X23) = (k1_xboole_0)))),
% 0.69/0.90      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.69/0.90  thf('37', plain,
% 0.69/0.90      ((((k1_xboole_0) != (k1_xboole_0))
% 0.69/0.90        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B)
% 0.69/0.90        | ((sk_A) = (k1_xboole_0))
% 0.69/0.90        | ((sk_B) = (k1_xboole_0))
% 0.69/0.90        | ((sk_C) = (k1_xboole_0)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['35', '36'])).
% 0.69/0.90  thf('38', plain,
% 0.69/0.90      ((((sk_C) = (k1_xboole_0))
% 0.69/0.90        | ((sk_B) = (k1_xboole_0))
% 0.69/0.90        | ((sk_A) = (k1_xboole_0))
% 0.69/0.90        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B))),
% 0.69/0.90      inference('simplify', [status(thm)], ['37'])).
% 0.69/0.90  thf('39', plain, (((sk_A) != (k1_xboole_0))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('40', plain, (((sk_B) != (k1_xboole_0))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('41', plain, (((sk_C) != (k1_xboole_0))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('42', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B)),
% 0.69/0.90      inference('simplify_reflect-', [status(thm)], ['38', '39', '40', '41'])).
% 0.69/0.90  thf(t1_subset, axiom,
% 0.69/0.90    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.69/0.90  thf('43', plain,
% 0.69/0.90      (![X2 : $i, X3 : $i]: ((m1_subset_1 @ X2 @ X3) | ~ (r2_hidden @ X2 @ X3))),
% 0.69/0.90      inference('cnf', [status(esa)], [t1_subset])).
% 0.69/0.90  thf('44', plain, ((m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B)),
% 0.69/0.90      inference('sup-', [status(thm)], ['42', '43'])).
% 0.69/0.90  thf('45', plain,
% 0.69/0.90      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.69/0.90         (~ (m1_subset_1 @ X31 @ sk_B)
% 0.69/0.90          | ((sk_D) = (X32))
% 0.69/0.90          | ((sk_E) != (k3_mcart_1 @ X32 @ X31 @ X33))
% 0.69/0.90          | ~ (m1_subset_1 @ X33 @ sk_C)
% 0.69/0.90          | ~ (m1_subset_1 @ X32 @ sk_A))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('46', plain,
% 0.69/0.90      (![X0 : $i, X1 : $i]:
% 0.69/0.90         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.69/0.90          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.69/0.90          | ((sk_E)
% 0.69/0.90              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1))
% 0.69/0.90          | ((sk_D) = (X0)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['44', '45'])).
% 0.69/0.90  thf('47', plain,
% 0.69/0.90      (![X0 : $i]:
% 0.69/0.90         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.69/0.90          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.69/0.90          | ((sk_D) = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.69/0.90          | ~ (m1_subset_1 @ X0 @ sk_C)
% 0.69/0.90          | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.69/0.90      inference('sup-', [status(thm)], ['30', '46'])).
% 0.69/0.90  thf('48', plain,
% 0.69/0.90      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.69/0.90        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['20', '23'])).
% 0.69/0.90  thf('49', plain,
% 0.69/0.90      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.69/0.90         ((r2_hidden @ (k1_mcart_1 @ X18) @ X19)
% 0.69/0.90          | ~ (r2_hidden @ X18 @ (k2_zfmisc_1 @ X19 @ X20)))),
% 0.69/0.90      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.69/0.90  thf('50', plain,
% 0.69/0.90      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.69/0.90        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.69/0.90      inference('sup-', [status(thm)], ['48', '49'])).
% 0.69/0.90  thf('51', plain,
% 0.69/0.90      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.69/0.90      inference('sup-', [status(thm)], ['9', '10'])).
% 0.69/0.90  thf('52', plain,
% 0.69/0.90      (((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 0.69/0.90        | ((k1_xboole_0) = (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['50', '51'])).
% 0.69/0.90  thf('53', plain,
% 0.69/0.90      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.69/0.90         (((k3_zfmisc_1 @ X23 @ X24 @ X25) != (k1_xboole_0))
% 0.69/0.90          | ((X25) = (k1_xboole_0))
% 0.69/0.90          | ((X24) = (k1_xboole_0))
% 0.69/0.90          | ((X23) = (k1_xboole_0)))),
% 0.69/0.90      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.69/0.90  thf('54', plain,
% 0.69/0.90      ((((k1_xboole_0) != (k1_xboole_0))
% 0.69/0.90        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 0.69/0.90        | ((sk_A) = (k1_xboole_0))
% 0.69/0.90        | ((sk_B) = (k1_xboole_0))
% 0.69/0.90        | ((sk_C) = (k1_xboole_0)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['52', '53'])).
% 0.69/0.90  thf('55', plain,
% 0.69/0.90      ((((sk_C) = (k1_xboole_0))
% 0.69/0.90        | ((sk_B) = (k1_xboole_0))
% 0.69/0.90        | ((sk_A) = (k1_xboole_0))
% 0.69/0.90        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.69/0.90      inference('simplify', [status(thm)], ['54'])).
% 0.69/0.90  thf('56', plain, (((sk_A) != (k1_xboole_0))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('57', plain, (((sk_B) != (k1_xboole_0))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('58', plain, (((sk_C) != (k1_xboole_0))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('59', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)),
% 0.69/0.90      inference('simplify_reflect-', [status(thm)], ['55', '56', '57', '58'])).
% 0.69/0.90  thf('60', plain,
% 0.69/0.90      (![X2 : $i, X3 : $i]: ((m1_subset_1 @ X2 @ X3) | ~ (r2_hidden @ X2 @ X3))),
% 0.69/0.90      inference('cnf', [status(esa)], [t1_subset])).
% 0.69/0.90  thf('61', plain, ((m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)),
% 0.69/0.90      inference('sup-', [status(thm)], ['59', '60'])).
% 0.69/0.90  thf('62', plain,
% 0.69/0.90      (![X0 : $i]:
% 0.69/0.90         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.69/0.90          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.69/0.90          | ((sk_D) = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.69/0.90          | ~ (m1_subset_1 @ X0 @ sk_C))),
% 0.69/0.90      inference('demod', [status(thm)], ['47', '61'])).
% 0.69/0.90  thf('63', plain, (((sk_D) != (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('64', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf(t50_mcart_1, axiom,
% 0.69/0.90    (![A:$i,B:$i,C:$i]:
% 0.69/0.90     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.69/0.90          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.69/0.90          ( ~( ![D:$i]:
% 0.69/0.90               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.69/0.90                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.69/0.90                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.69/0.90                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.69/0.90                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.69/0.90                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.69/0.90  thf('65', plain,
% 0.69/0.90      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.69/0.90         (((X27) = (k1_xboole_0))
% 0.69/0.90          | ((X28) = (k1_xboole_0))
% 0.69/0.90          | ((k5_mcart_1 @ X27 @ X28 @ X30 @ X29)
% 0.69/0.90              = (k1_mcart_1 @ (k1_mcart_1 @ X29)))
% 0.69/0.90          | ~ (m1_subset_1 @ X29 @ (k3_zfmisc_1 @ X27 @ X28 @ X30))
% 0.69/0.90          | ((X30) = (k1_xboole_0)))),
% 0.69/0.90      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.69/0.90  thf('66', plain,
% 0.69/0.90      ((((sk_C) = (k1_xboole_0))
% 0.69/0.90        | ((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.69/0.90            = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.69/0.90        | ((sk_B) = (k1_xboole_0))
% 0.69/0.90        | ((sk_A) = (k1_xboole_0)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['64', '65'])).
% 0.69/0.90  thf('67', plain, (((sk_A) != (k1_xboole_0))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('68', plain, (((sk_B) != (k1_xboole_0))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('69', plain, (((sk_C) != (k1_xboole_0))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('70', plain,
% 0.69/0.90      (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.69/0.90         = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 0.69/0.90      inference('simplify_reflect-', [status(thm)], ['66', '67', '68', '69'])).
% 0.69/0.90  thf('71', plain, (((sk_D) != (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 0.69/0.90      inference('demod', [status(thm)], ['63', '70'])).
% 0.69/0.90  thf('72', plain,
% 0.69/0.90      (![X0 : $i]:
% 0.69/0.90         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.69/0.90          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.69/0.90          | ~ (m1_subset_1 @ X0 @ sk_C))),
% 0.69/0.90      inference('simplify_reflect-', [status(thm)], ['62', '71'])).
% 0.69/0.90  thf('73', plain,
% 0.69/0.90      ((((sk_E) != (sk_E))
% 0.69/0.90        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)
% 0.69/0.90        | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['19', '72'])).
% 0.69/0.90  thf('74', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf(dt_k7_mcart_1, axiom,
% 0.69/0.90    (![A:$i,B:$i,C:$i,D:$i]:
% 0.69/0.90     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.69/0.90       ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ))).
% 0.69/0.90  thf('75', plain,
% 0.69/0.90      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.69/0.90         ((m1_subset_1 @ (k7_mcart_1 @ X14 @ X15 @ X16 @ X17) @ X16)
% 0.69/0.90          | ~ (m1_subset_1 @ X17 @ (k3_zfmisc_1 @ X14 @ X15 @ X16)))),
% 0.69/0.90      inference('cnf', [status(esa)], [dt_k7_mcart_1])).
% 0.69/0.90  thf('76', plain,
% 0.69/0.90      ((m1_subset_1 @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_C)),
% 0.69/0.90      inference('sup-', [status(thm)], ['74', '75'])).
% 0.69/0.90  thf('77', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('78', plain,
% 0.69/0.90      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.69/0.90         (((X27) = (k1_xboole_0))
% 0.69/0.90          | ((X28) = (k1_xboole_0))
% 0.69/0.90          | ((k7_mcart_1 @ X27 @ X28 @ X30 @ X29) = (k2_mcart_1 @ X29))
% 0.69/0.90          | ~ (m1_subset_1 @ X29 @ (k3_zfmisc_1 @ X27 @ X28 @ X30))
% 0.69/0.90          | ((X30) = (k1_xboole_0)))),
% 0.69/0.90      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.69/0.90  thf('79', plain,
% 0.69/0.90      ((((sk_C) = (k1_xboole_0))
% 0.69/0.90        | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))
% 0.69/0.90        | ((sk_B) = (k1_xboole_0))
% 0.69/0.90        | ((sk_A) = (k1_xboole_0)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['77', '78'])).
% 0.69/0.90  thf('80', plain, (((sk_A) != (k1_xboole_0))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('81', plain, (((sk_B) != (k1_xboole_0))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('82', plain, (((sk_C) != (k1_xboole_0))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('83', plain,
% 0.69/0.90      (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))),
% 0.69/0.90      inference('simplify_reflect-', [status(thm)], ['79', '80', '81', '82'])).
% 0.69/0.90  thf('84', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)),
% 0.69/0.90      inference('demod', [status(thm)], ['76', '83'])).
% 0.69/0.90  thf('85', plain,
% 0.69/0.90      ((((sk_E) != (sk_E)) | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 0.69/0.90      inference('demod', [status(thm)], ['73', '84'])).
% 0.69/0.90  thf('86', plain, ((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.69/0.90      inference('simplify', [status(thm)], ['85'])).
% 0.69/0.90  thf('87', plain,
% 0.69/0.90      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.69/0.90      inference('sup-', [status(thm)], ['9', '10'])).
% 0.69/0.90  thf('88', plain, (((k1_xboole_0) = (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.69/0.90      inference('sup-', [status(thm)], ['86', '87'])).
% 0.69/0.90  thf('89', plain,
% 0.69/0.90      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.69/0.90         (((k3_zfmisc_1 @ X23 @ X24 @ X25) != (k1_xboole_0))
% 0.69/0.90          | ((X25) = (k1_xboole_0))
% 0.69/0.90          | ((X24) = (k1_xboole_0))
% 0.69/0.90          | ((X23) = (k1_xboole_0)))),
% 0.69/0.90      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.69/0.90  thf('90', plain,
% 0.69/0.90      ((((k1_xboole_0) != (k1_xboole_0))
% 0.69/0.90        | ((sk_A) = (k1_xboole_0))
% 0.69/0.90        | ((sk_B) = (k1_xboole_0))
% 0.69/0.90        | ((sk_C) = (k1_xboole_0)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['88', '89'])).
% 0.69/0.90  thf('91', plain,
% 0.69/0.90      ((((sk_C) = (k1_xboole_0))
% 0.69/0.90        | ((sk_B) = (k1_xboole_0))
% 0.69/0.90        | ((sk_A) = (k1_xboole_0)))),
% 0.69/0.90      inference('simplify', [status(thm)], ['90'])).
% 0.69/0.90  thf('92', plain, (((sk_A) != (k1_xboole_0))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('93', plain, (((sk_B) != (k1_xboole_0))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('94', plain, (((sk_C) != (k1_xboole_0))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('95', plain, ($false),
% 0.69/0.90      inference('simplify_reflect-', [status(thm)], ['91', '92', '93', '94'])).
% 0.69/0.90  
% 0.69/0.90  % SZS output end Refutation
% 0.69/0.90  
% 0.69/0.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
