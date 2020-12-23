%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2FViCTpZyK

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:50 EST 2020

% Result     : Theorem 0.89s
% Output     : Refutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 245 expanded)
%              Number of leaves         :   31 (  88 expanded)
%              Depth                    :   18
%              Number of atoms          : 1145 (3686 expanded)
%              Number of equality atoms :  151 ( 482 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

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

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t23_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( A
          = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X23: $i,X24: $i] :
      ( ( X23
        = ( k4_tarski @ ( k1_mcart_1 @ X23 ) @ ( k2_mcart_1 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X24 )
      | ~ ( r2_hidden @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_zfmisc_1 @ X13 @ X14 @ X15 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( v1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) )
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
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
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
      = ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf(t35_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) )
    <=> ( ( k3_zfmisc_1 @ A @ B @ C )
       != k1_xboole_0 ) ) )).

thf('13',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k3_zfmisc_1 @ X25 @ X26 @ X27 )
       != k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('14',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( sk_E
    = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['15','16','17','18'])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('21',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_zfmisc_1 @ X13 @ X14 @ X15 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('22',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X20 ) @ X21 )
      | ~ ( r2_hidden @ X20 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k3_zfmisc_1 @ X25 @ X26 @ X27 )
       != k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('31',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('simplify_reflect+',[status(thm)],['29','30'])).

thf('32',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['31','32','33','34'])).

thf('36',plain,(
    ! [X23: $i,X24: $i] :
      ( ( X23
        = ( k4_tarski @ ( k1_mcart_1 @ X23 ) @ ( k2_mcart_1 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X24 )
      | ~ ( r2_hidden @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('39',plain,
    ( ( k1_mcart_1 @ sk_E )
    = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('40',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_mcart_1 @ X10 @ X11 @ X12 )
      = ( k4_tarski @ ( k4_tarski @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X0 )
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('44',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( k1_xboole_0
      = ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X20 ) @ X22 )
      | ~ ( r2_hidden @ X20 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('46',plain,
    ( ( k1_xboole_0
      = ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k3_zfmisc_1 @ X25 @ X26 @ X27 )
       != k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('48',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_1 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['49','50','51','52'])).

thf('54',plain,(
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

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('56',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ X5 @ X6 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ sk_B_1 )
      | ( sk_D = X34 )
      | ( sk_E
       != ( k3_mcart_1 @ X34 @ X33 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ sk_C )
      | ~ ( m1_subset_1 @ X34 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_E
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 ) )
      | ( sk_D = X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( sk_D
        = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','59'])).

thf('61',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( k1_xboole_0
      = ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('62',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X20 ) @ X21 )
      | ~ ( r2_hidden @ X20 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('63',plain,
    ( ( k1_xboole_0
      = ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k3_zfmisc_1 @ X25 @ X26 @ X27 )
       != k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('65',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['66','67','68','69'])).

thf('71',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ X5 @ X6 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('72',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( sk_D
        = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['60','72'])).

thf('74',plain,(
    sk_D
 != ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
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

thf('76',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( X29 = k1_xboole_0 )
      | ( X30 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X29 @ X30 @ X32 @ X31 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k3_zfmisc_1 @ X29 @ X30 @ X32 ) )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('77',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['77','78','79','80'])).

thf('82',plain,(
    sk_D
 != ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['74','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['73','82'])).

thf('84',plain,
    ( ( sk_E != sk_E )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['19','83'])).

thf('85',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('86',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_zfmisc_1 @ X13 @ X14 @ X15 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('87',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X20 ) @ X22 )
      | ~ ( r2_hidden @ X20 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) )
    | ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('91',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ( k1_xboole_0
      = ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k3_zfmisc_1 @ X25 @ X26 @ X27 )
       != k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('93',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['94','95','96','97'])).

thf('99',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ X5 @ X6 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('100',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    sk_E != sk_E ),
    inference(demod,[status(thm)],['84','100'])).

thf('102',plain,(
    $false ),
    inference(simplify,[status(thm)],['101'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2FViCTpZyK
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:03:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.89/1.14  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.89/1.14  % Solved by: fo/fo7.sh
% 0.89/1.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.89/1.14  % done 886 iterations in 0.682s
% 0.89/1.14  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.89/1.14  % SZS output start Refutation
% 0.89/1.14  thf(sk_A_type, type, sk_A: $i).
% 0.89/1.14  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.89/1.14  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.89/1.14  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.89/1.14  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.89/1.14  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.89/1.14  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.89/1.14  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.89/1.14  thf(sk_E_type, type, sk_E: $i).
% 0.89/1.14  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.89/1.14  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.89/1.14  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.89/1.14  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.89/1.14  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.89/1.14  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.89/1.14  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.89/1.14  thf(sk_C_type, type, sk_C: $i).
% 0.89/1.14  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.89/1.14  thf(sk_D_type, type, sk_D: $i).
% 0.89/1.14  thf(t69_mcart_1, conjecture,
% 0.89/1.14    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.89/1.14     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.89/1.14       ( ( ![F:$i]:
% 0.89/1.14           ( ( m1_subset_1 @ F @ A ) =>
% 0.89/1.14             ( ![G:$i]:
% 0.89/1.14               ( ( m1_subset_1 @ G @ B ) =>
% 0.89/1.14                 ( ![H:$i]:
% 0.89/1.14                   ( ( m1_subset_1 @ H @ C ) =>
% 0.89/1.14                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.89/1.14                       ( ( D ) = ( F ) ) ) ) ) ) ) ) ) =>
% 0.89/1.14         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.89/1.14           ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.89/1.14           ( ( D ) = ( k5_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 0.89/1.14  thf(zf_stmt_0, negated_conjecture,
% 0.89/1.14    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.89/1.14        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.89/1.14          ( ( ![F:$i]:
% 0.89/1.14              ( ( m1_subset_1 @ F @ A ) =>
% 0.89/1.14                ( ![G:$i]:
% 0.89/1.14                  ( ( m1_subset_1 @ G @ B ) =>
% 0.89/1.14                    ( ![H:$i]:
% 0.89/1.14                      ( ( m1_subset_1 @ H @ C ) =>
% 0.89/1.14                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.89/1.14                          ( ( D ) = ( F ) ) ) ) ) ) ) ) ) =>
% 0.89/1.14            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.89/1.14              ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.89/1.14              ( ( D ) = ( k5_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 0.89/1.14    inference('cnf.neg', [status(esa)], [t69_mcart_1])).
% 0.89/1.14  thf('0', plain,
% 0.89/1.14      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf(d2_subset_1, axiom,
% 0.89/1.14    (![A:$i,B:$i]:
% 0.89/1.14     ( ( ( v1_xboole_0 @ A ) =>
% 0.89/1.14         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.89/1.14       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.89/1.14         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.89/1.14  thf('1', plain,
% 0.89/1.14      (![X5 : $i, X6 : $i]:
% 0.89/1.14         (~ (m1_subset_1 @ X5 @ X6)
% 0.89/1.14          | (r2_hidden @ X5 @ X6)
% 0.89/1.14          | (v1_xboole_0 @ X6))),
% 0.89/1.14      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.89/1.14  thf('2', plain,
% 0.89/1.14      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.89/1.14        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.89/1.14      inference('sup-', [status(thm)], ['0', '1'])).
% 0.89/1.14  thf(t23_mcart_1, axiom,
% 0.89/1.14    (![A:$i,B:$i]:
% 0.89/1.14     ( ( v1_relat_1 @ B ) =>
% 0.89/1.14       ( ( r2_hidden @ A @ B ) =>
% 0.89/1.14         ( ( A ) = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ))).
% 0.89/1.14  thf('3', plain,
% 0.89/1.14      (![X23 : $i, X24 : $i]:
% 0.89/1.14         (((X23) = (k4_tarski @ (k1_mcart_1 @ X23) @ (k2_mcart_1 @ X23)))
% 0.89/1.14          | ~ (v1_relat_1 @ X24)
% 0.89/1.14          | ~ (r2_hidden @ X23 @ X24))),
% 0.89/1.14      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.89/1.14  thf('4', plain,
% 0.89/1.14      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.89/1.14        | ~ (v1_relat_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.89/1.14        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.89/1.14      inference('sup-', [status(thm)], ['2', '3'])).
% 0.89/1.14  thf(d3_zfmisc_1, axiom,
% 0.89/1.14    (![A:$i,B:$i,C:$i]:
% 0.89/1.14     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.89/1.14       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.89/1.14  thf('5', plain,
% 0.89/1.14      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.89/1.14         ((k3_zfmisc_1 @ X13 @ X14 @ X15)
% 0.89/1.14           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14) @ X15))),
% 0.89/1.14      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.89/1.14  thf(fc6_relat_1, axiom,
% 0.89/1.14    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.89/1.14  thf('6', plain,
% 0.89/1.14      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.89/1.14      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.89/1.14  thf('7', plain,
% 0.89/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.14         (v1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))),
% 0.89/1.14      inference('sup+', [status(thm)], ['5', '6'])).
% 0.89/1.14  thf('8', plain,
% 0.89/1.14      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.89/1.14        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.89/1.14      inference('demod', [status(thm)], ['4', '7'])).
% 0.89/1.14  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.89/1.14  thf('9', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.89/1.14      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.89/1.14  thf(t8_boole, axiom,
% 0.89/1.14    (![A:$i,B:$i]:
% 0.89/1.14     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.89/1.14  thf('10', plain,
% 0.89/1.14      (![X3 : $i, X4 : $i]:
% 0.89/1.14         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 0.89/1.14      inference('cnf', [status(esa)], [t8_boole])).
% 0.89/1.14  thf('11', plain,
% 0.89/1.14      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.89/1.14      inference('sup-', [status(thm)], ['9', '10'])).
% 0.89/1.14  thf('12', plain,
% 0.89/1.14      ((((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.89/1.14        | ((k1_xboole_0) = (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.89/1.14      inference('sup-', [status(thm)], ['8', '11'])).
% 0.89/1.14  thf(t35_mcart_1, axiom,
% 0.89/1.14    (![A:$i,B:$i,C:$i]:
% 0.89/1.14     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.89/1.14         ( ( C ) != ( k1_xboole_0 ) ) ) <=>
% 0.89/1.14       ( ( k3_zfmisc_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) ))).
% 0.89/1.14  thf('13', plain,
% 0.89/1.14      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.89/1.14         (((k3_zfmisc_1 @ X25 @ X26 @ X27) != (k1_xboole_0))
% 0.89/1.14          | ((X27) = (k1_xboole_0))
% 0.89/1.14          | ((X26) = (k1_xboole_0))
% 0.89/1.14          | ((X25) = (k1_xboole_0)))),
% 0.89/1.14      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.89/1.14  thf('14', plain,
% 0.89/1.14      ((((k1_xboole_0) != (k1_xboole_0))
% 0.89/1.14        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.89/1.14        | ((sk_A) = (k1_xboole_0))
% 0.89/1.14        | ((sk_B_1) = (k1_xboole_0))
% 0.89/1.14        | ((sk_C) = (k1_xboole_0)))),
% 0.89/1.14      inference('sup-', [status(thm)], ['12', '13'])).
% 0.89/1.14  thf('15', plain,
% 0.89/1.14      ((((sk_C) = (k1_xboole_0))
% 0.89/1.14        | ((sk_B_1) = (k1_xboole_0))
% 0.89/1.14        | ((sk_A) = (k1_xboole_0))
% 0.89/1.14        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.89/1.14      inference('simplify', [status(thm)], ['14'])).
% 0.89/1.14  thf('16', plain, (((sk_A) != (k1_xboole_0))),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('17', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('18', plain, (((sk_C) != (k1_xboole_0))),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('19', plain,
% 0.89/1.14      (((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))),
% 0.89/1.14      inference('simplify_reflect-', [status(thm)], ['15', '16', '17', '18'])).
% 0.89/1.14  thf('20', plain,
% 0.89/1.14      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.89/1.14        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.89/1.14      inference('sup-', [status(thm)], ['0', '1'])).
% 0.89/1.14  thf('21', plain,
% 0.89/1.14      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.89/1.14         ((k3_zfmisc_1 @ X13 @ X14 @ X15)
% 0.89/1.14           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14) @ X15))),
% 0.89/1.14      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.89/1.14  thf(t10_mcart_1, axiom,
% 0.89/1.14    (![A:$i,B:$i,C:$i]:
% 0.89/1.14     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.89/1.14       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.89/1.14         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.89/1.14  thf('22', plain,
% 0.89/1.14      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.89/1.14         ((r2_hidden @ (k1_mcart_1 @ X20) @ X21)
% 0.89/1.14          | ~ (r2_hidden @ X20 @ (k2_zfmisc_1 @ X21 @ X22)))),
% 0.89/1.14      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.89/1.14  thf('23', plain,
% 0.89/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.89/1.14         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.89/1.14          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.89/1.14      inference('sup-', [status(thm)], ['21', '22'])).
% 0.89/1.14  thf('24', plain,
% 0.89/1.14      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.89/1.14        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.89/1.14      inference('sup-', [status(thm)], ['20', '23'])).
% 0.89/1.14  thf('25', plain,
% 0.89/1.14      (![X3 : $i, X4 : $i]:
% 0.89/1.14         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 0.89/1.14      inference('cnf', [status(esa)], [t8_boole])).
% 0.89/1.14  thf('26', plain,
% 0.89/1.14      (![X0 : $i]:
% 0.89/1.14         ((r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.89/1.14          | ((k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C) = (X0))
% 0.89/1.14          | ~ (v1_xboole_0 @ X0))),
% 0.89/1.14      inference('sup-', [status(thm)], ['24', '25'])).
% 0.89/1.14  thf('27', plain,
% 0.89/1.14      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.89/1.14         (((k3_zfmisc_1 @ X25 @ X26 @ X27) != (k1_xboole_0))
% 0.89/1.14          | ((X27) = (k1_xboole_0))
% 0.89/1.14          | ((X26) = (k1_xboole_0))
% 0.89/1.14          | ((X25) = (k1_xboole_0)))),
% 0.89/1.14      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.89/1.14  thf('28', plain,
% 0.89/1.14      (![X0 : $i]:
% 0.89/1.14         (((X0) != (k1_xboole_0))
% 0.89/1.14          | ~ (v1_xboole_0 @ X0)
% 0.89/1.14          | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.89/1.14          | ((sk_A) = (k1_xboole_0))
% 0.89/1.14          | ((sk_B_1) = (k1_xboole_0))
% 0.89/1.14          | ((sk_C) = (k1_xboole_0)))),
% 0.89/1.14      inference('sup-', [status(thm)], ['26', '27'])).
% 0.89/1.14  thf('29', plain,
% 0.89/1.14      ((((sk_C) = (k1_xboole_0))
% 0.89/1.14        | ((sk_B_1) = (k1_xboole_0))
% 0.89/1.14        | ((sk_A) = (k1_xboole_0))
% 0.89/1.14        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.89/1.14        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.89/1.14      inference('simplify', [status(thm)], ['28'])).
% 0.89/1.14  thf('30', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.89/1.14      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.89/1.14  thf('31', plain,
% 0.89/1.14      ((((sk_C) = (k1_xboole_0))
% 0.89/1.14        | ((sk_B_1) = (k1_xboole_0))
% 0.89/1.14        | ((sk_A) = (k1_xboole_0))
% 0.89/1.14        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.89/1.14      inference('simplify_reflect+', [status(thm)], ['29', '30'])).
% 0.89/1.14  thf('32', plain, (((sk_A) != (k1_xboole_0))),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('33', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('34', plain, (((sk_C) != (k1_xboole_0))),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('35', plain,
% 0.89/1.14      ((r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.89/1.14      inference('simplify_reflect-', [status(thm)], ['31', '32', '33', '34'])).
% 0.89/1.14  thf('36', plain,
% 0.89/1.14      (![X23 : $i, X24 : $i]:
% 0.89/1.14         (((X23) = (k4_tarski @ (k1_mcart_1 @ X23) @ (k2_mcart_1 @ X23)))
% 0.89/1.14          | ~ (v1_relat_1 @ X24)
% 0.89/1.14          | ~ (r2_hidden @ X23 @ X24))),
% 0.89/1.14      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.89/1.14  thf('37', plain,
% 0.89/1.14      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.89/1.14        | ((k1_mcart_1 @ sk_E)
% 0.89/1.14            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.89/1.14               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 0.89/1.14      inference('sup-', [status(thm)], ['35', '36'])).
% 0.89/1.14  thf('38', plain,
% 0.89/1.14      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.89/1.14      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.89/1.14  thf('39', plain,
% 0.89/1.14      (((k1_mcart_1 @ sk_E)
% 0.89/1.14         = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.89/1.14            (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 0.89/1.14      inference('demod', [status(thm)], ['37', '38'])).
% 0.89/1.14  thf(d3_mcart_1, axiom,
% 0.89/1.14    (![A:$i,B:$i,C:$i]:
% 0.89/1.14     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.89/1.14  thf('40', plain,
% 0.89/1.14      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.89/1.14         ((k3_mcart_1 @ X10 @ X11 @ X12)
% 0.89/1.14           = (k4_tarski @ (k4_tarski @ X10 @ X11) @ X12))),
% 0.89/1.14      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.89/1.14  thf('41', plain,
% 0.89/1.14      (![X0 : $i]:
% 0.89/1.14         ((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.89/1.14           (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X0)
% 0.89/1.14           = (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))),
% 0.89/1.14      inference('sup+', [status(thm)], ['39', '40'])).
% 0.89/1.14  thf('42', plain,
% 0.89/1.14      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.89/1.14        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.89/1.14      inference('sup-', [status(thm)], ['20', '23'])).
% 0.89/1.14  thf('43', plain,
% 0.89/1.14      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.89/1.14      inference('sup-', [status(thm)], ['9', '10'])).
% 0.89/1.14  thf('44', plain,
% 0.89/1.14      (((r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.89/1.14        | ((k1_xboole_0) = (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.89/1.14      inference('sup-', [status(thm)], ['42', '43'])).
% 0.89/1.14  thf('45', plain,
% 0.89/1.14      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.89/1.14         ((r2_hidden @ (k2_mcart_1 @ X20) @ X22)
% 0.89/1.14          | ~ (r2_hidden @ X20 @ (k2_zfmisc_1 @ X21 @ X22)))),
% 0.89/1.14      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.89/1.14  thf('46', plain,
% 0.89/1.14      ((((k1_xboole_0) = (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.89/1.14        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_1))),
% 0.89/1.14      inference('sup-', [status(thm)], ['44', '45'])).
% 0.89/1.14  thf('47', plain,
% 0.89/1.14      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.89/1.14         (((k3_zfmisc_1 @ X25 @ X26 @ X27) != (k1_xboole_0))
% 0.89/1.14          | ((X27) = (k1_xboole_0))
% 0.89/1.14          | ((X26) = (k1_xboole_0))
% 0.89/1.14          | ((X25) = (k1_xboole_0)))),
% 0.89/1.14      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.89/1.14  thf('48', plain,
% 0.89/1.14      ((((k1_xboole_0) != (k1_xboole_0))
% 0.89/1.14        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_1)
% 0.89/1.14        | ((sk_A) = (k1_xboole_0))
% 0.89/1.14        | ((sk_B_1) = (k1_xboole_0))
% 0.89/1.14        | ((sk_C) = (k1_xboole_0)))),
% 0.89/1.14      inference('sup-', [status(thm)], ['46', '47'])).
% 0.89/1.14  thf('49', plain,
% 0.89/1.14      ((((sk_C) = (k1_xboole_0))
% 0.89/1.14        | ((sk_B_1) = (k1_xboole_0))
% 0.89/1.14        | ((sk_A) = (k1_xboole_0))
% 0.89/1.14        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_1))),
% 0.89/1.14      inference('simplify', [status(thm)], ['48'])).
% 0.89/1.14  thf('50', plain, (((sk_A) != (k1_xboole_0))),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('51', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('52', plain, (((sk_C) != (k1_xboole_0))),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('53', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_1)),
% 0.89/1.14      inference('simplify_reflect-', [status(thm)], ['49', '50', '51', '52'])).
% 0.89/1.14  thf('54', plain,
% 0.89/1.14      (![X5 : $i, X6 : $i]:
% 0.89/1.14         (~ (r2_hidden @ X5 @ X6)
% 0.89/1.14          | (m1_subset_1 @ X5 @ X6)
% 0.89/1.14          | (v1_xboole_0 @ X6))),
% 0.89/1.14      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.89/1.14  thf(d1_xboole_0, axiom,
% 0.89/1.14    (![A:$i]:
% 0.89/1.14     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.89/1.14  thf('55', plain,
% 0.89/1.14      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.89/1.14      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.89/1.14  thf('56', plain,
% 0.89/1.14      (![X5 : $i, X6 : $i]: ((m1_subset_1 @ X5 @ X6) | ~ (r2_hidden @ X5 @ X6))),
% 0.89/1.14      inference('clc', [status(thm)], ['54', '55'])).
% 0.89/1.14  thf('57', plain,
% 0.89/1.14      ((m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_1)),
% 0.89/1.14      inference('sup-', [status(thm)], ['53', '56'])).
% 0.89/1.14  thf('58', plain,
% 0.89/1.14      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.89/1.14         (~ (m1_subset_1 @ X33 @ sk_B_1)
% 0.89/1.14          | ((sk_D) = (X34))
% 0.89/1.14          | ((sk_E) != (k3_mcart_1 @ X34 @ X33 @ X35))
% 0.89/1.14          | ~ (m1_subset_1 @ X35 @ sk_C)
% 0.89/1.14          | ~ (m1_subset_1 @ X34 @ sk_A))),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('59', plain,
% 0.89/1.14      (![X0 : $i, X1 : $i]:
% 0.89/1.14         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.89/1.14          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.89/1.14          | ((sk_E)
% 0.89/1.14              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1))
% 0.89/1.14          | ((sk_D) = (X0)))),
% 0.89/1.14      inference('sup-', [status(thm)], ['57', '58'])).
% 0.89/1.14  thf('60', plain,
% 0.89/1.14      (![X0 : $i]:
% 0.89/1.14         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.89/1.14          | ((sk_D) = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.89/1.14          | ~ (m1_subset_1 @ X0 @ sk_C)
% 0.89/1.14          | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.89/1.14      inference('sup-', [status(thm)], ['41', '59'])).
% 0.89/1.14  thf('61', plain,
% 0.89/1.14      (((r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.89/1.14        | ((k1_xboole_0) = (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.89/1.14      inference('sup-', [status(thm)], ['42', '43'])).
% 0.89/1.14  thf('62', plain,
% 0.89/1.14      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.89/1.14         ((r2_hidden @ (k1_mcart_1 @ X20) @ X21)
% 0.89/1.14          | ~ (r2_hidden @ X20 @ (k2_zfmisc_1 @ X21 @ X22)))),
% 0.89/1.14      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.89/1.14  thf('63', plain,
% 0.89/1.14      ((((k1_xboole_0) = (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.89/1.14        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.89/1.14      inference('sup-', [status(thm)], ['61', '62'])).
% 0.89/1.14  thf('64', plain,
% 0.89/1.14      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.89/1.14         (((k3_zfmisc_1 @ X25 @ X26 @ X27) != (k1_xboole_0))
% 0.89/1.14          | ((X27) = (k1_xboole_0))
% 0.89/1.14          | ((X26) = (k1_xboole_0))
% 0.89/1.14          | ((X25) = (k1_xboole_0)))),
% 0.89/1.14      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.89/1.14  thf('65', plain,
% 0.89/1.14      ((((k1_xboole_0) != (k1_xboole_0))
% 0.89/1.14        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 0.89/1.14        | ((sk_A) = (k1_xboole_0))
% 0.89/1.14        | ((sk_B_1) = (k1_xboole_0))
% 0.89/1.14        | ((sk_C) = (k1_xboole_0)))),
% 0.89/1.14      inference('sup-', [status(thm)], ['63', '64'])).
% 0.89/1.14  thf('66', plain,
% 0.89/1.14      ((((sk_C) = (k1_xboole_0))
% 0.89/1.14        | ((sk_B_1) = (k1_xboole_0))
% 0.89/1.14        | ((sk_A) = (k1_xboole_0))
% 0.89/1.14        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.89/1.14      inference('simplify', [status(thm)], ['65'])).
% 0.89/1.14  thf('67', plain, (((sk_A) != (k1_xboole_0))),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('68', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('69', plain, (((sk_C) != (k1_xboole_0))),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('70', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)),
% 0.89/1.14      inference('simplify_reflect-', [status(thm)], ['66', '67', '68', '69'])).
% 0.89/1.14  thf('71', plain,
% 0.89/1.14      (![X5 : $i, X6 : $i]: ((m1_subset_1 @ X5 @ X6) | ~ (r2_hidden @ X5 @ X6))),
% 0.89/1.14      inference('clc', [status(thm)], ['54', '55'])).
% 0.89/1.14  thf('72', plain, ((m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)),
% 0.89/1.14      inference('sup-', [status(thm)], ['70', '71'])).
% 0.89/1.14  thf('73', plain,
% 0.89/1.14      (![X0 : $i]:
% 0.89/1.14         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.89/1.14          | ((sk_D) = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.89/1.14          | ~ (m1_subset_1 @ X0 @ sk_C))),
% 0.89/1.14      inference('demod', [status(thm)], ['60', '72'])).
% 0.89/1.14  thf('74', plain, (((sk_D) != (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E))),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('75', plain,
% 0.89/1.14      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf(t50_mcart_1, axiom,
% 0.89/1.14    (![A:$i,B:$i,C:$i]:
% 0.89/1.14     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.89/1.14          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.89/1.14          ( ~( ![D:$i]:
% 0.89/1.14               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.89/1.14                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.89/1.14                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.89/1.14                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.89/1.14                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.89/1.14                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.89/1.14  thf('76', plain,
% 0.89/1.14      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.89/1.14         (((X29) = (k1_xboole_0))
% 0.89/1.14          | ((X30) = (k1_xboole_0))
% 0.89/1.14          | ((k5_mcart_1 @ X29 @ X30 @ X32 @ X31)
% 0.89/1.14              = (k1_mcart_1 @ (k1_mcart_1 @ X31)))
% 0.89/1.14          | ~ (m1_subset_1 @ X31 @ (k3_zfmisc_1 @ X29 @ X30 @ X32))
% 0.89/1.14          | ((X32) = (k1_xboole_0)))),
% 0.89/1.14      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.89/1.14  thf('77', plain,
% 0.89/1.14      ((((sk_C) = (k1_xboole_0))
% 0.89/1.14        | ((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E)
% 0.89/1.14            = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.89/1.14        | ((sk_B_1) = (k1_xboole_0))
% 0.89/1.14        | ((sk_A) = (k1_xboole_0)))),
% 0.89/1.14      inference('sup-', [status(thm)], ['75', '76'])).
% 0.89/1.14  thf('78', plain, (((sk_A) != (k1_xboole_0))),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('79', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('80', plain, (((sk_C) != (k1_xboole_0))),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('81', plain,
% 0.89/1.14      (((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_E)
% 0.89/1.14         = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 0.89/1.14      inference('simplify_reflect-', [status(thm)], ['77', '78', '79', '80'])).
% 0.89/1.14  thf('82', plain, (((sk_D) != (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 0.89/1.14      inference('demod', [status(thm)], ['74', '81'])).
% 0.89/1.14  thf('83', plain,
% 0.89/1.14      (![X0 : $i]:
% 0.89/1.14         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.89/1.14          | ~ (m1_subset_1 @ X0 @ sk_C))),
% 0.89/1.14      inference('simplify_reflect-', [status(thm)], ['73', '82'])).
% 0.89/1.14  thf('84', plain,
% 0.89/1.14      ((((sk_E) != (sk_E)) | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C))),
% 0.89/1.14      inference('sup-', [status(thm)], ['19', '83'])).
% 0.89/1.14  thf('85', plain,
% 0.89/1.14      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.89/1.14        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.89/1.14      inference('sup-', [status(thm)], ['0', '1'])).
% 0.89/1.14  thf('86', plain,
% 0.89/1.14      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.89/1.14         ((k3_zfmisc_1 @ X13 @ X14 @ X15)
% 0.89/1.14           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14) @ X15))),
% 0.89/1.14      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.89/1.14  thf('87', plain,
% 0.89/1.14      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.89/1.14         ((r2_hidden @ (k2_mcart_1 @ X20) @ X22)
% 0.89/1.14          | ~ (r2_hidden @ X20 @ (k2_zfmisc_1 @ X21 @ X22)))),
% 0.89/1.14      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.89/1.14  thf('88', plain,
% 0.89/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.89/1.14         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.89/1.14          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 0.89/1.14      inference('sup-', [status(thm)], ['86', '87'])).
% 0.89/1.14  thf('89', plain,
% 0.89/1.14      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))
% 0.89/1.14        | (r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C))),
% 0.89/1.14      inference('sup-', [status(thm)], ['85', '88'])).
% 0.89/1.14  thf('90', plain,
% 0.89/1.14      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.89/1.14      inference('sup-', [status(thm)], ['9', '10'])).
% 0.89/1.14  thf('91', plain,
% 0.89/1.14      (((r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C)
% 0.89/1.14        | ((k1_xboole_0) = (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.89/1.14      inference('sup-', [status(thm)], ['89', '90'])).
% 0.89/1.14  thf('92', plain,
% 0.89/1.14      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.89/1.14         (((k3_zfmisc_1 @ X25 @ X26 @ X27) != (k1_xboole_0))
% 0.89/1.14          | ((X27) = (k1_xboole_0))
% 0.89/1.14          | ((X26) = (k1_xboole_0))
% 0.89/1.14          | ((X25) = (k1_xboole_0)))),
% 0.89/1.14      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.89/1.14  thf('93', plain,
% 0.89/1.14      ((((k1_xboole_0) != (k1_xboole_0))
% 0.89/1.14        | (r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C)
% 0.89/1.14        | ((sk_A) = (k1_xboole_0))
% 0.89/1.14        | ((sk_B_1) = (k1_xboole_0))
% 0.89/1.14        | ((sk_C) = (k1_xboole_0)))),
% 0.89/1.14      inference('sup-', [status(thm)], ['91', '92'])).
% 0.89/1.14  thf('94', plain,
% 0.89/1.14      ((((sk_C) = (k1_xboole_0))
% 0.89/1.14        | ((sk_B_1) = (k1_xboole_0))
% 0.89/1.14        | ((sk_A) = (k1_xboole_0))
% 0.89/1.14        | (r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C))),
% 0.89/1.14      inference('simplify', [status(thm)], ['93'])).
% 0.89/1.14  thf('95', plain, (((sk_A) != (k1_xboole_0))),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('96', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('97', plain, (((sk_C) != (k1_xboole_0))),
% 0.89/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.14  thf('98', plain, ((r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C)),
% 0.89/1.14      inference('simplify_reflect-', [status(thm)], ['94', '95', '96', '97'])).
% 0.89/1.14  thf('99', plain,
% 0.89/1.14      (![X5 : $i, X6 : $i]: ((m1_subset_1 @ X5 @ X6) | ~ (r2_hidden @ X5 @ X6))),
% 0.89/1.14      inference('clc', [status(thm)], ['54', '55'])).
% 0.89/1.14  thf('100', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)),
% 0.89/1.14      inference('sup-', [status(thm)], ['98', '99'])).
% 0.89/1.14  thf('101', plain, (((sk_E) != (sk_E))),
% 0.89/1.14      inference('demod', [status(thm)], ['84', '100'])).
% 0.89/1.14  thf('102', plain, ($false), inference('simplify', [status(thm)], ['101'])).
% 0.89/1.14  
% 0.89/1.14  % SZS output end Refutation
% 0.89/1.14  
% 0.89/1.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
