%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IuCByB1DC4

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:00 EST 2020

% Result     : Theorem 0.89s
% Output     : Refutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :  196 (2938 expanded)
%              Number of leaves         :   31 ( 889 expanded)
%              Depth                    :   45
%              Number of atoms          : 1871 (45928 expanded)
%              Number of equality atoms :  162 (4903 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('1',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

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

thf('3',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ X6 ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( ( X22
        = ( k4_tarski @ ( k1_mcart_1 @ X22 ) @ ( k2_mcart_1 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X23 )
      | ~ ( r2_hidden @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('10',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_zfmisc_1 @ X12 @ X13 @ X14 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
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

thf('15',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('16',plain,
    ( ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('18',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
    | ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('21',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_zfmisc_1 @ X12 @ X13 @ X14 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('22',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X19 ) @ X20 )
      | ~ ( r2_hidden @ X19 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X19 ) @ X20 )
      | ~ ( r2_hidden @ X19 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('26',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('28',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('30',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
    | ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['30'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('32',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ X3 @ X4 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('33',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
    | ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('35',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('36',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('37',plain,(
    ! [X22: $i,X23: $i] :
      ( ( X22
        = ( k4_tarski @ ( k1_mcart_1 @ X22 ) @ ( k2_mcart_1 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X23 )
      | ~ ( r2_hidden @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('38',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('42',plain,
    ( ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('43',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_mcart_1 @ X9 @ X10 @ X11 )
      = ( k4_tarski @ ( k4_tarski @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X0 )
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('46',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X19 ) @ X21 )
      | ~ ( r2_hidden @ X19 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('47',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('49',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('51',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B )
    | ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ X3 @ X4 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('54',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ sk_B )
      | ( sk_E
       != ( k3_mcart_1 @ X29 @ X28 @ X30 ) )
      | ( sk_D = X30 )
      | ~ ( m1_subset_1 @ X30 @ sk_C )
      | ~ ( m1_subset_1 @ X29 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_D = X1 )
      | ( sk_E
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ( sk_D = X0 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 )
      | ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ( sk_E != sk_E )
    | ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ) )).

thf('62',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( m1_subset_1 @ ( k7_mcart_1 @ X15 @ X16 @ X17 @ X18 ) @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k3_zfmisc_1 @ X15 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_mcart_1])).

thf('63',plain,(
    m1_subset_1 @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_C ),
    inference('sup-',[status(thm)],['61','62'])).

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
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X24 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X24 @ X25 @ X27 @ X26 )
        = ( k2_mcart_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k3_zfmisc_1 @ X24 @ X25 @ X27 ) )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('66',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k2_mcart_1 @ sk_E ) )
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
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['66','67','68','69'])).

thf('71',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['63','70'])).

thf('72',plain,
    ( ( sk_E != sk_E )
    | ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','71'])).

thf('73',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) )
    | ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    sk_D
 != ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['66','67','68','69'])).

thf('76',plain,(
    sk_D
 != ( k2_mcart_1 @ sk_E ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 )
    | ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['73','76'])).

thf('78',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('79',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
    | ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_mcart_1 @ X9 @ X10 @ X11 )
      = ( k4_tarski @ ( k4_tarski @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X0 )
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_D = X1 )
      | ( sk_E
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ( sk_D = X0 )
      | ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['33','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_C )
      | ( sk_D = X0 )
      | ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ( sk_E != sk_E )
    | ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['19','87'])).

thf('89',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['63','70'])).

thf('90',plain,
    ( ( sk_E != sk_E )
    | ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( sk_D
      = ( k2_mcart_1 @ sk_E ) )
    | ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    sk_D
 != ( k2_mcart_1 @ sk_E ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('93',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['91','92'])).

thf('94',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['5','93'])).

thf('95',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('96',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('97',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_zfmisc_1 @ X12 @ X13 @ X14 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(fc10_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B ) )
     => ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('98',plain,(
    ! [X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[fc10_subset_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
    | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['96','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ( sk_E
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['95','102'])).

thf('104',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('106',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['91','92'])).

thf('110',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['104','110'])).

thf('112',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('113',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
    | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[fc10_subset_1])).

thf('116',plain,
    ( ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('118',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['91','92'])).

thf('122',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference(clc,[status(thm)],['116','122'])).

thf('124',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['5','93'])).

thf('125',plain,
    ( sk_E
    = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ),
    inference(clc,[status(thm)],['123','124'])).

thf('126',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('127',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('128',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
    | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ X3 @ X4 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('130',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('132',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('133',plain,
    ( ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
    | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_mcart_1 @ X9 @ X10 @ X11 )
      = ( k4_tarski @ ( k4_tarski @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X0 )
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('137',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('138',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B )
    | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ X3 @ X4 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('140',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ sk_B )
      | ( sk_E
       != ( k3_mcart_1 @ X29 @ X28 @ X30 ) )
      | ( sk_D = X30 )
      | ~ ( m1_subset_1 @ X30 @ sk_C )
      | ~ ( m1_subset_1 @ X29 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_D = X1 )
      | ( sk_E
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ sk_C )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['135','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ( sk_D = X0 )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ sk_C )
      | ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ sk_C )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['130','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_C )
      | ( sk_D = X0 )
      | ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,
    ( ( sk_E != sk_E )
    | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['125','146'])).

thf('148',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['63','70'])).

thf('149',plain,
    ( ( sk_E != sk_E )
    | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,
    ( ( sk_D
      = ( k2_mcart_1 @ sk_E ) )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,(
    sk_D
 != ( k2_mcart_1 @ sk_E ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('152',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['150','151'])).

thf('153',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('154',plain,(
    v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('156',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[fc10_subset_1])).

thf('158',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['91','92'])).

thf('160',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['158','159'])).

thf('161',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('162',plain,(
    v1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['160','161'])).

thf('163',plain,(
    $false ),
    inference(demod,[status(thm)],['94','162'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IuCByB1DC4
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:05:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.89/1.09  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.89/1.09  % Solved by: fo/fo7.sh
% 0.89/1.09  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.89/1.09  % done 805 iterations in 0.630s
% 0.89/1.09  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.89/1.09  % SZS output start Refutation
% 0.89/1.09  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.89/1.09  thf(sk_A_type, type, sk_A: $i).
% 0.89/1.09  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.89/1.09  thf(sk_B_type, type, sk_B: $i).
% 0.89/1.09  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.89/1.09  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.89/1.09  thf(sk_C_type, type, sk_C: $i).
% 0.89/1.09  thf(sk_D_type, type, sk_D: $i).
% 0.89/1.09  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.89/1.09  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.89/1.09  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.89/1.09  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.89/1.09  thf(sk_E_type, type, sk_E: $i).
% 0.89/1.09  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.89/1.09  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.89/1.09  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.89/1.09  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.89/1.09  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.89/1.09  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.89/1.09  thf(l13_xboole_0, axiom,
% 0.89/1.09    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.89/1.09  thf('0', plain,
% 0.89/1.09      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.89/1.09      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.89/1.09  thf('1', plain,
% 0.89/1.09      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.89/1.09      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.89/1.09  thf('2', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.89/1.09      inference('sup+', [status(thm)], ['0', '1'])).
% 0.89/1.09  thf(t71_mcart_1, conjecture,
% 0.89/1.09    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.89/1.09     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.89/1.09       ( ( ![F:$i]:
% 0.89/1.09           ( ( m1_subset_1 @ F @ A ) =>
% 0.89/1.09             ( ![G:$i]:
% 0.89/1.09               ( ( m1_subset_1 @ G @ B ) =>
% 0.89/1.09                 ( ![H:$i]:
% 0.89/1.09                   ( ( m1_subset_1 @ H @ C ) =>
% 0.89/1.09                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.89/1.09                       ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 0.89/1.09         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.89/1.09           ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.89/1.09           ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 0.89/1.09  thf(zf_stmt_0, negated_conjecture,
% 0.89/1.09    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.89/1.09        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.89/1.09          ( ( ![F:$i]:
% 0.89/1.09              ( ( m1_subset_1 @ F @ A ) =>
% 0.89/1.09                ( ![G:$i]:
% 0.89/1.09                  ( ( m1_subset_1 @ G @ B ) =>
% 0.89/1.09                    ( ![H:$i]:
% 0.89/1.09                      ( ( m1_subset_1 @ H @ C ) =>
% 0.89/1.09                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.89/1.09                          ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 0.89/1.09            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.89/1.09              ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.89/1.09              ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 0.89/1.09    inference('cnf.neg', [status(esa)], [t71_mcart_1])).
% 0.89/1.09  thf('3', plain, (((sk_A) != (k1_xboole_0))),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('4', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         (((X0) != (k1_xboole_0))
% 0.89/1.09          | ~ (v1_xboole_0 @ X0)
% 0.89/1.09          | ~ (v1_xboole_0 @ sk_A))),
% 0.89/1.09      inference('sup-', [status(thm)], ['2', '3'])).
% 0.89/1.09  thf('5', plain, ((~ (v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.89/1.09      inference('simplify', [status(thm)], ['4'])).
% 0.89/1.09  thf('6', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf(t2_subset, axiom,
% 0.89/1.09    (![A:$i,B:$i]:
% 0.89/1.09     ( ( m1_subset_1 @ A @ B ) =>
% 0.89/1.09       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.89/1.09  thf('7', plain,
% 0.89/1.09      (![X5 : $i, X6 : $i]:
% 0.89/1.09         ((r2_hidden @ X5 @ X6)
% 0.89/1.09          | (v1_xboole_0 @ X6)
% 0.89/1.09          | ~ (m1_subset_1 @ X5 @ X6))),
% 0.89/1.09      inference('cnf', [status(esa)], [t2_subset])).
% 0.89/1.09  thf('8', plain,
% 0.89/1.09      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.89/1.09        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['6', '7'])).
% 0.89/1.09  thf(t23_mcart_1, axiom,
% 0.89/1.09    (![A:$i,B:$i]:
% 0.89/1.09     ( ( v1_relat_1 @ B ) =>
% 0.89/1.09       ( ( r2_hidden @ A @ B ) =>
% 0.89/1.09         ( ( A ) = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ))).
% 0.89/1.09  thf('9', plain,
% 0.89/1.09      (![X22 : $i, X23 : $i]:
% 0.89/1.09         (((X22) = (k4_tarski @ (k1_mcart_1 @ X22) @ (k2_mcart_1 @ X22)))
% 0.89/1.09          | ~ (v1_relat_1 @ X23)
% 0.89/1.09          | ~ (r2_hidden @ X22 @ X23))),
% 0.89/1.09      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.89/1.09  thf('10', plain,
% 0.89/1.09      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.89/1.09        | ~ (v1_relat_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.89/1.09        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.89/1.09      inference('sup-', [status(thm)], ['8', '9'])).
% 0.89/1.09  thf(d3_zfmisc_1, axiom,
% 0.89/1.09    (![A:$i,B:$i,C:$i]:
% 0.89/1.09     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.89/1.09       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.89/1.09  thf('11', plain,
% 0.89/1.09      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.89/1.09         ((k3_zfmisc_1 @ X12 @ X13 @ X14)
% 0.89/1.09           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13) @ X14))),
% 0.89/1.09      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.89/1.09  thf(fc6_relat_1, axiom,
% 0.89/1.09    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.89/1.09  thf('12', plain,
% 0.89/1.09      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.89/1.09      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.89/1.09  thf('13', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.09         (v1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))),
% 0.89/1.09      inference('sup+', [status(thm)], ['11', '12'])).
% 0.89/1.09  thf('14', plain,
% 0.89/1.09      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.89/1.09        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.89/1.09      inference('demod', [status(thm)], ['10', '13'])).
% 0.89/1.09  thf('15', plain,
% 0.89/1.09      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.89/1.09      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.89/1.09  thf('16', plain,
% 0.89/1.09      ((((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.89/1.09        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['14', '15'])).
% 0.89/1.09  thf('17', plain,
% 0.89/1.09      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.89/1.09        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.89/1.09      inference('demod', [status(thm)], ['10', '13'])).
% 0.89/1.09  thf('18', plain,
% 0.89/1.09      (((v1_xboole_0 @ k1_xboole_0)
% 0.89/1.09        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.89/1.09        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.89/1.09      inference('sup+', [status(thm)], ['16', '17'])).
% 0.89/1.09  thf('19', plain,
% 0.89/1.09      ((((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.89/1.09        | (v1_xboole_0 @ k1_xboole_0))),
% 0.89/1.09      inference('simplify', [status(thm)], ['18'])).
% 0.89/1.09  thf('20', plain,
% 0.89/1.09      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.89/1.09        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['6', '7'])).
% 0.89/1.09  thf('21', plain,
% 0.89/1.09      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.89/1.09         ((k3_zfmisc_1 @ X12 @ X13 @ X14)
% 0.89/1.09           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13) @ X14))),
% 0.89/1.09      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.89/1.09  thf(t10_mcart_1, axiom,
% 0.89/1.09    (![A:$i,B:$i,C:$i]:
% 0.89/1.09     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.89/1.09       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.89/1.09         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.89/1.09  thf('22', plain,
% 0.89/1.09      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.89/1.09         ((r2_hidden @ (k1_mcart_1 @ X19) @ X20)
% 0.89/1.09          | ~ (r2_hidden @ X19 @ (k2_zfmisc_1 @ X20 @ X21)))),
% 0.89/1.09      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.89/1.09  thf('23', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.89/1.09         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.89/1.09          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['21', '22'])).
% 0.89/1.09  thf('24', plain,
% 0.89/1.09      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.89/1.09        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['20', '23'])).
% 0.89/1.09  thf('25', plain,
% 0.89/1.09      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.89/1.09         ((r2_hidden @ (k1_mcart_1 @ X19) @ X20)
% 0.89/1.09          | ~ (r2_hidden @ X19 @ (k2_zfmisc_1 @ X20 @ X21)))),
% 0.89/1.09      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.89/1.09  thf('26', plain,
% 0.89/1.09      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.89/1.09        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.89/1.09      inference('sup-', [status(thm)], ['24', '25'])).
% 0.89/1.09  thf('27', plain,
% 0.89/1.09      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.89/1.09      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.89/1.09  thf('28', plain,
% 0.89/1.09      (((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 0.89/1.09        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['26', '27'])).
% 0.89/1.09  thf('29', plain,
% 0.89/1.09      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.89/1.09        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.89/1.09      inference('sup-', [status(thm)], ['24', '25'])).
% 0.89/1.09  thf('30', plain,
% 0.89/1.09      (((v1_xboole_0 @ k1_xboole_0)
% 0.89/1.09        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 0.89/1.09        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.89/1.09      inference('sup+', [status(thm)], ['28', '29'])).
% 0.89/1.09  thf('31', plain,
% 0.89/1.09      (((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 0.89/1.09        | (v1_xboole_0 @ k1_xboole_0))),
% 0.89/1.09      inference('simplify', [status(thm)], ['30'])).
% 0.89/1.09  thf(t1_subset, axiom,
% 0.89/1.09    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.89/1.09  thf('32', plain,
% 0.89/1.09      (![X3 : $i, X4 : $i]: ((m1_subset_1 @ X3 @ X4) | ~ (r2_hidden @ X3 @ X4))),
% 0.89/1.09      inference('cnf', [status(esa)], [t1_subset])).
% 0.89/1.09  thf('33', plain,
% 0.89/1.09      (((v1_xboole_0 @ k1_xboole_0)
% 0.89/1.09        | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.89/1.09      inference('sup-', [status(thm)], ['31', '32'])).
% 0.89/1.09  thf('34', plain,
% 0.89/1.09      ((((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.89/1.09        | (v1_xboole_0 @ k1_xboole_0))),
% 0.89/1.09      inference('simplify', [status(thm)], ['18'])).
% 0.89/1.09  thf('35', plain,
% 0.89/1.09      (((v1_xboole_0 @ k1_xboole_0)
% 0.89/1.09        | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.89/1.09      inference('sup-', [status(thm)], ['31', '32'])).
% 0.89/1.09  thf('36', plain,
% 0.89/1.09      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.89/1.09        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['20', '23'])).
% 0.89/1.09  thf('37', plain,
% 0.89/1.09      (![X22 : $i, X23 : $i]:
% 0.89/1.09         (((X22) = (k4_tarski @ (k1_mcart_1 @ X22) @ (k2_mcart_1 @ X22)))
% 0.89/1.09          | ~ (v1_relat_1 @ X23)
% 0.89/1.09          | ~ (r2_hidden @ X22 @ X23))),
% 0.89/1.09      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.89/1.09  thf('38', plain,
% 0.89/1.09      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.89/1.09        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.89/1.09        | ((k1_mcart_1 @ sk_E)
% 0.89/1.09            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.89/1.09               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 0.89/1.09      inference('sup-', [status(thm)], ['36', '37'])).
% 0.89/1.09  thf('39', plain,
% 0.89/1.09      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.89/1.09      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.89/1.09  thf('40', plain,
% 0.89/1.09      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.89/1.09        | ((k1_mcart_1 @ sk_E)
% 0.89/1.09            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.89/1.09               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 0.89/1.09      inference('demod', [status(thm)], ['38', '39'])).
% 0.89/1.09  thf('41', plain,
% 0.89/1.09      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.89/1.09      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.89/1.09  thf('42', plain,
% 0.89/1.09      ((((k1_mcart_1 @ sk_E)
% 0.89/1.09          = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.89/1.09             (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 0.89/1.09        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['40', '41'])).
% 0.89/1.09  thf(d3_mcart_1, axiom,
% 0.89/1.09    (![A:$i,B:$i,C:$i]:
% 0.89/1.09     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.89/1.09  thf('43', plain,
% 0.89/1.09      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.89/1.09         ((k3_mcart_1 @ X9 @ X10 @ X11)
% 0.89/1.09           = (k4_tarski @ (k4_tarski @ X9 @ X10) @ X11))),
% 0.89/1.09      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.89/1.09  thf('44', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         (((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.89/1.09            (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X0)
% 0.89/1.09            = (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.89/1.09          | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 0.89/1.09      inference('sup+', [status(thm)], ['42', '43'])).
% 0.89/1.09  thf('45', plain,
% 0.89/1.09      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.89/1.09        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['20', '23'])).
% 0.89/1.09  thf('46', plain,
% 0.89/1.09      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.89/1.09         ((r2_hidden @ (k2_mcart_1 @ X19) @ X21)
% 0.89/1.09          | ~ (r2_hidden @ X19 @ (k2_zfmisc_1 @ X20 @ X21)))),
% 0.89/1.09      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.89/1.09  thf('47', plain,
% 0.89/1.09      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.89/1.09        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B))),
% 0.89/1.09      inference('sup-', [status(thm)], ['45', '46'])).
% 0.89/1.09  thf('48', plain,
% 0.89/1.09      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.89/1.09      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.89/1.09  thf('49', plain,
% 0.89/1.09      (((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B)
% 0.89/1.09        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['47', '48'])).
% 0.89/1.09  thf('50', plain,
% 0.89/1.09      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.89/1.09        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B))),
% 0.89/1.09      inference('sup-', [status(thm)], ['45', '46'])).
% 0.89/1.09  thf('51', plain,
% 0.89/1.09      (((v1_xboole_0 @ k1_xboole_0)
% 0.89/1.09        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B)
% 0.89/1.09        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B))),
% 0.89/1.09      inference('sup+', [status(thm)], ['49', '50'])).
% 0.89/1.09  thf('52', plain,
% 0.89/1.09      (((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B)
% 0.89/1.09        | (v1_xboole_0 @ k1_xboole_0))),
% 0.89/1.09      inference('simplify', [status(thm)], ['51'])).
% 0.89/1.09  thf('53', plain,
% 0.89/1.09      (![X3 : $i, X4 : $i]: ((m1_subset_1 @ X3 @ X4) | ~ (r2_hidden @ X3 @ X4))),
% 0.89/1.09      inference('cnf', [status(esa)], [t1_subset])).
% 0.89/1.09  thf('54', plain,
% 0.89/1.09      (((v1_xboole_0 @ k1_xboole_0)
% 0.89/1.09        | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B))),
% 0.89/1.09      inference('sup-', [status(thm)], ['52', '53'])).
% 0.89/1.09  thf('55', plain,
% 0.89/1.09      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.89/1.09         (~ (m1_subset_1 @ X28 @ sk_B)
% 0.89/1.09          | ((sk_E) != (k3_mcart_1 @ X29 @ X28 @ X30))
% 0.89/1.09          | ((sk_D) = (X30))
% 0.89/1.09          | ~ (m1_subset_1 @ X30 @ sk_C)
% 0.89/1.09          | ~ (m1_subset_1 @ X29 @ sk_A))),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('56', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((v1_xboole_0 @ k1_xboole_0)
% 0.89/1.09          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.89/1.09          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.89/1.09          | ((sk_D) = (X1))
% 0.89/1.09          | ((sk_E)
% 0.89/1.09              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['54', '55'])).
% 0.89/1.09  thf('57', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.89/1.09          | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))
% 0.89/1.09          | ((sk_D) = (X0))
% 0.89/1.09          | ~ (m1_subset_1 @ X0 @ sk_C)
% 0.89/1.09          | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 0.89/1.09          | (v1_xboole_0 @ k1_xboole_0))),
% 0.89/1.09      inference('sup-', [status(thm)], ['44', '56'])).
% 0.89/1.09  thf('58', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         ((v1_xboole_0 @ k1_xboole_0)
% 0.89/1.09          | (v1_xboole_0 @ k1_xboole_0)
% 0.89/1.09          | ~ (m1_subset_1 @ X0 @ sk_C)
% 0.89/1.09          | ((sk_D) = (X0))
% 0.89/1.09          | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))
% 0.89/1.09          | ((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['35', '57'])).
% 0.89/1.09  thf('59', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.89/1.09          | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))
% 0.89/1.09          | ((sk_D) = (X0))
% 0.89/1.09          | ~ (m1_subset_1 @ X0 @ sk_C)
% 0.89/1.09          | (v1_xboole_0 @ k1_xboole_0))),
% 0.89/1.09      inference('simplify', [status(thm)], ['58'])).
% 0.89/1.09  thf('60', plain,
% 0.89/1.09      ((((sk_E) != (sk_E))
% 0.89/1.09        | (v1_xboole_0 @ k1_xboole_0)
% 0.89/1.09        | (v1_xboole_0 @ k1_xboole_0)
% 0.89/1.09        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)
% 0.89/1.09        | ((sk_D) = (k2_mcart_1 @ sk_E))
% 0.89/1.09        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['34', '59'])).
% 0.89/1.09  thf('61', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf(dt_k7_mcart_1, axiom,
% 0.89/1.09    (![A:$i,B:$i,C:$i,D:$i]:
% 0.89/1.09     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.89/1.09       ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ))).
% 0.89/1.09  thf('62', plain,
% 0.89/1.09      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.89/1.09         ((m1_subset_1 @ (k7_mcart_1 @ X15 @ X16 @ X17 @ X18) @ X17)
% 0.89/1.09          | ~ (m1_subset_1 @ X18 @ (k3_zfmisc_1 @ X15 @ X16 @ X17)))),
% 0.89/1.09      inference('cnf', [status(esa)], [dt_k7_mcart_1])).
% 0.89/1.09  thf('63', plain,
% 0.89/1.09      ((m1_subset_1 @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_C)),
% 0.89/1.09      inference('sup-', [status(thm)], ['61', '62'])).
% 0.89/1.09  thf('64', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf(t50_mcart_1, axiom,
% 0.89/1.09    (![A:$i,B:$i,C:$i]:
% 0.89/1.09     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.89/1.09          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.89/1.09          ( ~( ![D:$i]:
% 0.89/1.09               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.89/1.09                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.89/1.09                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.89/1.09                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.89/1.09                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.89/1.09                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.89/1.09  thf('65', plain,
% 0.89/1.09      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.89/1.09         (((X24) = (k1_xboole_0))
% 0.89/1.09          | ((X25) = (k1_xboole_0))
% 0.89/1.09          | ((k7_mcart_1 @ X24 @ X25 @ X27 @ X26) = (k2_mcart_1 @ X26))
% 0.89/1.09          | ~ (m1_subset_1 @ X26 @ (k3_zfmisc_1 @ X24 @ X25 @ X27))
% 0.89/1.09          | ((X27) = (k1_xboole_0)))),
% 0.89/1.09      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.89/1.09  thf('66', plain,
% 0.89/1.09      ((((sk_C) = (k1_xboole_0))
% 0.89/1.09        | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))
% 0.89/1.09        | ((sk_B) = (k1_xboole_0))
% 0.89/1.09        | ((sk_A) = (k1_xboole_0)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['64', '65'])).
% 0.89/1.09  thf('67', plain, (((sk_A) != (k1_xboole_0))),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('68', plain, (((sk_B) != (k1_xboole_0))),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('69', plain, (((sk_C) != (k1_xboole_0))),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('70', plain,
% 0.89/1.09      (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))),
% 0.89/1.09      inference('simplify_reflect-', [status(thm)], ['66', '67', '68', '69'])).
% 0.89/1.09  thf('71', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)),
% 0.89/1.09      inference('demod', [status(thm)], ['63', '70'])).
% 0.89/1.09  thf('72', plain,
% 0.89/1.09      ((((sk_E) != (sk_E))
% 0.89/1.09        | (v1_xboole_0 @ k1_xboole_0)
% 0.89/1.09        | (v1_xboole_0 @ k1_xboole_0)
% 0.89/1.09        | ((sk_D) = (k2_mcart_1 @ sk_E))
% 0.89/1.09        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 0.89/1.09      inference('demod', [status(thm)], ['60', '71'])).
% 0.89/1.09  thf('73', plain,
% 0.89/1.09      ((((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))
% 0.89/1.09        | ((sk_D) = (k2_mcart_1 @ sk_E))
% 0.89/1.09        | (v1_xboole_0 @ k1_xboole_0))),
% 0.89/1.09      inference('simplify', [status(thm)], ['72'])).
% 0.89/1.09  thf('74', plain, (((sk_D) != (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E))),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('75', plain,
% 0.89/1.09      (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))),
% 0.89/1.09      inference('simplify_reflect-', [status(thm)], ['66', '67', '68', '69'])).
% 0.89/1.09  thf('76', plain, (((sk_D) != (k2_mcart_1 @ sk_E))),
% 0.89/1.09      inference('demod', [status(thm)], ['74', '75'])).
% 0.89/1.09  thf('77', plain,
% 0.89/1.09      ((((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))
% 0.89/1.09        | (v1_xboole_0 @ k1_xboole_0))),
% 0.89/1.09      inference('simplify_reflect-', [status(thm)], ['73', '76'])).
% 0.89/1.09  thf('78', plain,
% 0.89/1.09      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.89/1.09        | ((k1_mcart_1 @ sk_E)
% 0.89/1.09            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.89/1.09               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 0.89/1.09      inference('demod', [status(thm)], ['38', '39'])).
% 0.89/1.09  thf('79', plain,
% 0.89/1.09      (((v1_xboole_0 @ k1_xboole_0)
% 0.89/1.09        | (v1_xboole_0 @ k1_xboole_0)
% 0.89/1.09        | ((k1_mcart_1 @ sk_E)
% 0.89/1.09            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.89/1.09               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 0.89/1.09      inference('sup+', [status(thm)], ['77', '78'])).
% 0.89/1.09  thf('80', plain,
% 0.89/1.09      ((((k1_mcart_1 @ sk_E)
% 0.89/1.09          = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.89/1.09             (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 0.89/1.09        | (v1_xboole_0 @ k1_xboole_0))),
% 0.89/1.09      inference('simplify', [status(thm)], ['79'])).
% 0.89/1.09  thf('81', plain,
% 0.89/1.09      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.89/1.09         ((k3_mcart_1 @ X9 @ X10 @ X11)
% 0.89/1.09           = (k4_tarski @ (k4_tarski @ X9 @ X10) @ X11))),
% 0.89/1.09      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.89/1.09  thf('82', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         (((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.89/1.09            (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X0)
% 0.89/1.09            = (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.89/1.09          | (v1_xboole_0 @ k1_xboole_0))),
% 0.89/1.09      inference('sup+', [status(thm)], ['80', '81'])).
% 0.89/1.09  thf('83', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((v1_xboole_0 @ k1_xboole_0)
% 0.89/1.09          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.89/1.09          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.89/1.09          | ((sk_D) = (X1))
% 0.89/1.09          | ((sk_E)
% 0.89/1.09              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['54', '55'])).
% 0.89/1.09  thf('84', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.89/1.09          | (v1_xboole_0 @ k1_xboole_0)
% 0.89/1.09          | ((sk_D) = (X0))
% 0.89/1.09          | ~ (m1_subset_1 @ X0 @ sk_C)
% 0.89/1.09          | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 0.89/1.09          | (v1_xboole_0 @ k1_xboole_0))),
% 0.89/1.09      inference('sup-', [status(thm)], ['82', '83'])).
% 0.89/1.09  thf('85', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         (~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 0.89/1.09          | ~ (m1_subset_1 @ X0 @ sk_C)
% 0.89/1.09          | ((sk_D) = (X0))
% 0.89/1.09          | (v1_xboole_0 @ k1_xboole_0)
% 0.89/1.09          | ((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0)))),
% 0.89/1.09      inference('simplify', [status(thm)], ['84'])).
% 0.89/1.09  thf('86', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         ((v1_xboole_0 @ k1_xboole_0)
% 0.89/1.09          | ((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.89/1.09          | (v1_xboole_0 @ k1_xboole_0)
% 0.89/1.09          | ((sk_D) = (X0))
% 0.89/1.09          | ~ (m1_subset_1 @ X0 @ sk_C))),
% 0.89/1.09      inference('sup-', [status(thm)], ['33', '85'])).
% 0.89/1.09  thf('87', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         (~ (m1_subset_1 @ X0 @ sk_C)
% 0.89/1.09          | ((sk_D) = (X0))
% 0.89/1.09          | ((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.89/1.09          | (v1_xboole_0 @ k1_xboole_0))),
% 0.89/1.09      inference('simplify', [status(thm)], ['86'])).
% 0.89/1.09  thf('88', plain,
% 0.89/1.09      ((((sk_E) != (sk_E))
% 0.89/1.09        | (v1_xboole_0 @ k1_xboole_0)
% 0.89/1.09        | (v1_xboole_0 @ k1_xboole_0)
% 0.89/1.09        | ((sk_D) = (k2_mcart_1 @ sk_E))
% 0.89/1.09        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C))),
% 0.89/1.09      inference('sup-', [status(thm)], ['19', '87'])).
% 0.89/1.09  thf('89', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)),
% 0.89/1.09      inference('demod', [status(thm)], ['63', '70'])).
% 0.89/1.09  thf('90', plain,
% 0.89/1.09      ((((sk_E) != (sk_E))
% 0.89/1.09        | (v1_xboole_0 @ k1_xboole_0)
% 0.89/1.09        | (v1_xboole_0 @ k1_xboole_0)
% 0.89/1.09        | ((sk_D) = (k2_mcart_1 @ sk_E)))),
% 0.89/1.09      inference('demod', [status(thm)], ['88', '89'])).
% 0.89/1.09  thf('91', plain,
% 0.89/1.09      ((((sk_D) = (k2_mcart_1 @ sk_E)) | (v1_xboole_0 @ k1_xboole_0))),
% 0.89/1.09      inference('simplify', [status(thm)], ['90'])).
% 0.89/1.09  thf('92', plain, (((sk_D) != (k2_mcart_1 @ sk_E))),
% 0.89/1.09      inference('demod', [status(thm)], ['74', '75'])).
% 0.89/1.09  thf('93', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.89/1.09      inference('simplify_reflect-', [status(thm)], ['91', '92'])).
% 0.89/1.09  thf('94', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.89/1.09      inference('demod', [status(thm)], ['5', '93'])).
% 0.89/1.09  thf('95', plain,
% 0.89/1.09      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.89/1.09        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.89/1.09      inference('demod', [status(thm)], ['10', '13'])).
% 0.89/1.09  thf('96', plain,
% 0.89/1.09      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.89/1.09        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.89/1.09      inference('demod', [status(thm)], ['10', '13'])).
% 0.89/1.09  thf('97', plain,
% 0.89/1.09      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.89/1.09         ((k3_zfmisc_1 @ X12 @ X13 @ X14)
% 0.89/1.09           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13) @ X14))),
% 0.89/1.09      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.89/1.09  thf(fc10_subset_1, axiom,
% 0.89/1.09    (![A:$i,B:$i]:
% 0.89/1.09     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.89/1.09       ( ~( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) ))).
% 0.89/1.09  thf('98', plain,
% 0.89/1.09      (![X1 : $i, X2 : $i]:
% 0.89/1.09         ((v1_xboole_0 @ X1)
% 0.89/1.09          | (v1_xboole_0 @ X2)
% 0.89/1.09          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X2)))),
% 0.89/1.09      inference('cnf', [status(esa)], [fc10_subset_1])).
% 0.89/1.09  thf('99', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.09         (~ (v1_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.89/1.09          | (v1_xboole_0 @ X0)
% 0.89/1.09          | (v1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['97', '98'])).
% 0.89/1.09  thf('100', plain,
% 0.89/1.09      ((((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.89/1.09        | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.89/1.09        | (v1_xboole_0 @ sk_C))),
% 0.89/1.09      inference('sup-', [status(thm)], ['96', '99'])).
% 0.89/1.09  thf('101', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.89/1.09      inference('sup+', [status(thm)], ['0', '1'])).
% 0.89/1.09  thf('102', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         ((v1_xboole_0 @ sk_C)
% 0.89/1.09          | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.89/1.09          | ~ (v1_xboole_0 @ X0)
% 0.89/1.09          | ((X0) = (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['100', '101'])).
% 0.89/1.09  thf('103', plain,
% 0.89/1.09      ((((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.89/1.09        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.89/1.09        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.89/1.09        | (v1_xboole_0 @ sk_C))),
% 0.89/1.09      inference('sup-', [status(thm)], ['95', '102'])).
% 0.89/1.09  thf('104', plain,
% 0.89/1.09      (((v1_xboole_0 @ sk_C)
% 0.89/1.09        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.89/1.09        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.89/1.09      inference('simplify', [status(thm)], ['103'])).
% 0.89/1.09  thf('105', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.89/1.09      inference('sup+', [status(thm)], ['0', '1'])).
% 0.89/1.09  thf('106', plain, (((sk_C) != (k1_xboole_0))),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('107', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         (((X0) != (k1_xboole_0))
% 0.89/1.09          | ~ (v1_xboole_0 @ X0)
% 0.89/1.09          | ~ (v1_xboole_0 @ sk_C))),
% 0.89/1.09      inference('sup-', [status(thm)], ['105', '106'])).
% 0.89/1.09  thf('108', plain, ((~ (v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.89/1.09      inference('simplify', [status(thm)], ['107'])).
% 0.89/1.09  thf('109', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.89/1.09      inference('simplify_reflect-', [status(thm)], ['91', '92'])).
% 0.89/1.09  thf('110', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.89/1.09      inference('demod', [status(thm)], ['108', '109'])).
% 0.89/1.09  thf('111', plain,
% 0.89/1.09      ((((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.89/1.09        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.09      inference('clc', [status(thm)], ['104', '110'])).
% 0.89/1.09  thf('112', plain,
% 0.89/1.09      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.89/1.09        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.89/1.09      inference('demod', [status(thm)], ['10', '13'])).
% 0.89/1.09  thf('113', plain,
% 0.89/1.09      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.89/1.09        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.89/1.09        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.89/1.09      inference('sup+', [status(thm)], ['111', '112'])).
% 0.89/1.09  thf('114', plain,
% 0.89/1.09      ((((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.89/1.09        | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.09      inference('simplify', [status(thm)], ['113'])).
% 0.89/1.09  thf('115', plain,
% 0.89/1.09      (![X1 : $i, X2 : $i]:
% 0.89/1.09         ((v1_xboole_0 @ X1)
% 0.89/1.09          | (v1_xboole_0 @ X2)
% 0.89/1.09          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X2)))),
% 0.89/1.09      inference('cnf', [status(esa)], [fc10_subset_1])).
% 0.89/1.09  thf('116', plain,
% 0.89/1.09      ((((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.89/1.09        | (v1_xboole_0 @ sk_B)
% 0.89/1.09        | (v1_xboole_0 @ sk_A))),
% 0.89/1.09      inference('sup-', [status(thm)], ['114', '115'])).
% 0.89/1.09  thf('117', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.89/1.09      inference('sup+', [status(thm)], ['0', '1'])).
% 0.89/1.09  thf('118', plain, (((sk_B) != (k1_xboole_0))),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('119', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         (((X0) != (k1_xboole_0))
% 0.89/1.09          | ~ (v1_xboole_0 @ X0)
% 0.89/1.09          | ~ (v1_xboole_0 @ sk_B))),
% 0.89/1.09      inference('sup-', [status(thm)], ['117', '118'])).
% 0.89/1.09  thf('120', plain, ((~ (v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.89/1.09      inference('simplify', [status(thm)], ['119'])).
% 0.89/1.09  thf('121', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.89/1.09      inference('simplify_reflect-', [status(thm)], ['91', '92'])).
% 0.89/1.09  thf('122', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.89/1.09      inference('demod', [status(thm)], ['120', '121'])).
% 0.89/1.09  thf('123', plain,
% 0.89/1.09      (((v1_xboole_0 @ sk_A)
% 0.89/1.09        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.89/1.09      inference('clc', [status(thm)], ['116', '122'])).
% 0.89/1.09  thf('124', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.89/1.09      inference('demod', [status(thm)], ['5', '93'])).
% 0.89/1.09  thf('125', plain,
% 0.89/1.09      (((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))),
% 0.89/1.09      inference('clc', [status(thm)], ['123', '124'])).
% 0.89/1.09  thf('126', plain,
% 0.89/1.09      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.89/1.09        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.89/1.09      inference('sup-', [status(thm)], ['24', '25'])).
% 0.89/1.09  thf('127', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.09         (~ (v1_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.89/1.09          | (v1_xboole_0 @ X0)
% 0.89/1.09          | (v1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['97', '98'])).
% 0.89/1.09  thf('128', plain,
% 0.89/1.09      (((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 0.89/1.09        | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.89/1.09        | (v1_xboole_0 @ sk_C))),
% 0.89/1.09      inference('sup-', [status(thm)], ['126', '127'])).
% 0.89/1.09  thf('129', plain,
% 0.89/1.09      (![X3 : $i, X4 : $i]: ((m1_subset_1 @ X3 @ X4) | ~ (r2_hidden @ X3 @ X4))),
% 0.89/1.09      inference('cnf', [status(esa)], [t1_subset])).
% 0.89/1.09  thf('130', plain,
% 0.89/1.09      (((v1_xboole_0 @ sk_C)
% 0.89/1.09        | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.89/1.09        | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.89/1.09      inference('sup-', [status(thm)], ['128', '129'])).
% 0.89/1.09  thf('131', plain,
% 0.89/1.09      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.89/1.09        | ((k1_mcart_1 @ sk_E)
% 0.89/1.09            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.89/1.09               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 0.89/1.09      inference('demod', [status(thm)], ['38', '39'])).
% 0.89/1.09  thf('132', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.09         (~ (v1_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.89/1.09          | (v1_xboole_0 @ X0)
% 0.89/1.09          | (v1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['97', '98'])).
% 0.89/1.09  thf('133', plain,
% 0.89/1.09      ((((k1_mcart_1 @ sk_E)
% 0.89/1.09          = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.89/1.09             (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 0.89/1.09        | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.89/1.09        | (v1_xboole_0 @ sk_C))),
% 0.89/1.09      inference('sup-', [status(thm)], ['131', '132'])).
% 0.89/1.09  thf('134', plain,
% 0.89/1.09      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.89/1.09         ((k3_mcart_1 @ X9 @ X10 @ X11)
% 0.89/1.09           = (k4_tarski @ (k4_tarski @ X9 @ X10) @ X11))),
% 0.89/1.09      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.89/1.09  thf('135', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         (((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.89/1.09            (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X0)
% 0.89/1.09            = (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.89/1.09          | (v1_xboole_0 @ sk_C)
% 0.89/1.09          | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.09      inference('sup+', [status(thm)], ['133', '134'])).
% 0.89/1.09  thf('136', plain,
% 0.89/1.09      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.89/1.09        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B))),
% 0.89/1.09      inference('sup-', [status(thm)], ['45', '46'])).
% 0.89/1.09  thf('137', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.09         (~ (v1_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.89/1.09          | (v1_xboole_0 @ X0)
% 0.89/1.09          | (v1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['97', '98'])).
% 0.89/1.09  thf('138', plain,
% 0.89/1.09      (((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B)
% 0.89/1.09        | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.89/1.09        | (v1_xboole_0 @ sk_C))),
% 0.89/1.09      inference('sup-', [status(thm)], ['136', '137'])).
% 0.89/1.09  thf('139', plain,
% 0.89/1.09      (![X3 : $i, X4 : $i]: ((m1_subset_1 @ X3 @ X4) | ~ (r2_hidden @ X3 @ X4))),
% 0.89/1.09      inference('cnf', [status(esa)], [t1_subset])).
% 0.89/1.09  thf('140', plain,
% 0.89/1.09      (((v1_xboole_0 @ sk_C)
% 0.89/1.09        | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.89/1.09        | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B))),
% 0.89/1.09      inference('sup-', [status(thm)], ['138', '139'])).
% 0.89/1.09  thf('141', plain,
% 0.89/1.09      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.89/1.09         (~ (m1_subset_1 @ X28 @ sk_B)
% 0.89/1.09          | ((sk_E) != (k3_mcart_1 @ X29 @ X28 @ X30))
% 0.89/1.09          | ((sk_D) = (X30))
% 0.89/1.09          | ~ (m1_subset_1 @ X30 @ sk_C)
% 0.89/1.09          | ~ (m1_subset_1 @ X29 @ sk_A))),
% 0.89/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.09  thf('142', plain,
% 0.89/1.09      (![X0 : $i, X1 : $i]:
% 0.89/1.09         ((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.89/1.09          | (v1_xboole_0 @ sk_C)
% 0.89/1.09          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.89/1.09          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.89/1.09          | ((sk_D) = (X1))
% 0.89/1.09          | ((sk_E)
% 0.89/1.09              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['140', '141'])).
% 0.89/1.09  thf('143', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.89/1.09          | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.89/1.09          | (v1_xboole_0 @ sk_C)
% 0.89/1.09          | ((sk_D) = (X0))
% 0.89/1.09          | ~ (m1_subset_1 @ X0 @ sk_C)
% 0.89/1.09          | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 0.89/1.09          | (v1_xboole_0 @ sk_C)
% 0.89/1.09          | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.09      inference('sup-', [status(thm)], ['135', '142'])).
% 0.89/1.09  thf('144', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         (~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 0.89/1.09          | ~ (m1_subset_1 @ X0 @ sk_C)
% 0.89/1.09          | ((sk_D) = (X0))
% 0.89/1.09          | (v1_xboole_0 @ sk_C)
% 0.89/1.09          | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.89/1.09          | ((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0)))),
% 0.89/1.09      inference('simplify', [status(thm)], ['143'])).
% 0.89/1.09  thf('145', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         ((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.89/1.09          | (v1_xboole_0 @ sk_C)
% 0.89/1.09          | ((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.89/1.09          | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.89/1.09          | (v1_xboole_0 @ sk_C)
% 0.89/1.09          | ((sk_D) = (X0))
% 0.89/1.09          | ~ (m1_subset_1 @ X0 @ sk_C))),
% 0.89/1.09      inference('sup-', [status(thm)], ['130', '144'])).
% 0.89/1.09  thf('146', plain,
% 0.89/1.09      (![X0 : $i]:
% 0.89/1.09         (~ (m1_subset_1 @ X0 @ sk_C)
% 0.89/1.09          | ((sk_D) = (X0))
% 0.89/1.09          | ((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.89/1.09          | (v1_xboole_0 @ sk_C)
% 0.89/1.09          | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.09      inference('simplify', [status(thm)], ['145'])).
% 0.89/1.09  thf('147', plain,
% 0.89/1.09      ((((sk_E) != (sk_E))
% 0.89/1.09        | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.89/1.09        | (v1_xboole_0 @ sk_C)
% 0.89/1.09        | ((sk_D) = (k2_mcart_1 @ sk_E))
% 0.89/1.09        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C))),
% 0.89/1.09      inference('sup-', [status(thm)], ['125', '146'])).
% 0.89/1.09  thf('148', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)),
% 0.89/1.09      inference('demod', [status(thm)], ['63', '70'])).
% 0.89/1.09  thf('149', plain,
% 0.89/1.09      ((((sk_E) != (sk_E))
% 0.89/1.09        | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.89/1.09        | (v1_xboole_0 @ sk_C)
% 0.89/1.09        | ((sk_D) = (k2_mcart_1 @ sk_E)))),
% 0.89/1.09      inference('demod', [status(thm)], ['147', '148'])).
% 0.89/1.09  thf('150', plain,
% 0.89/1.09      ((((sk_D) = (k2_mcart_1 @ sk_E))
% 0.89/1.09        | (v1_xboole_0 @ sk_C)
% 0.89/1.09        | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.09      inference('simplify', [status(thm)], ['149'])).
% 0.89/1.09  thf('151', plain, (((sk_D) != (k2_mcart_1 @ sk_E))),
% 0.89/1.09      inference('demod', [status(thm)], ['74', '75'])).
% 0.89/1.09  thf('152', plain,
% 0.89/1.09      (((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.09      inference('simplify_reflect-', [status(thm)], ['150', '151'])).
% 0.89/1.09  thf('153', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.89/1.09      inference('demod', [status(thm)], ['108', '109'])).
% 0.89/1.09  thf('154', plain, ((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.89/1.09      inference('clc', [status(thm)], ['152', '153'])).
% 0.89/1.09  thf('155', plain,
% 0.89/1.09      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.89/1.09      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.89/1.09  thf('156', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.89/1.09      inference('sup-', [status(thm)], ['154', '155'])).
% 0.89/1.09  thf('157', plain,
% 0.89/1.09      (![X1 : $i, X2 : $i]:
% 0.89/1.09         ((v1_xboole_0 @ X1)
% 0.89/1.09          | (v1_xboole_0 @ X2)
% 0.89/1.09          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X2)))),
% 0.89/1.09      inference('cnf', [status(esa)], [fc10_subset_1])).
% 0.89/1.09  thf('158', plain,
% 0.89/1.09      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.89/1.09        | (v1_xboole_0 @ sk_B)
% 0.89/1.09        | (v1_xboole_0 @ sk_A))),
% 0.89/1.09      inference('sup-', [status(thm)], ['156', '157'])).
% 0.89/1.09  thf('159', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.89/1.09      inference('simplify_reflect-', [status(thm)], ['91', '92'])).
% 0.89/1.09  thf('160', plain, (((v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A))),
% 0.89/1.09      inference('demod', [status(thm)], ['158', '159'])).
% 0.89/1.09  thf('161', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.89/1.09      inference('demod', [status(thm)], ['120', '121'])).
% 0.89/1.09  thf('162', plain, ((v1_xboole_0 @ sk_A)),
% 0.89/1.09      inference('clc', [status(thm)], ['160', '161'])).
% 0.89/1.09  thf('163', plain, ($false), inference('demod', [status(thm)], ['94', '162'])).
% 0.89/1.09  
% 0.89/1.09  % SZS output end Refutation
% 0.89/1.09  
% 0.89/1.10  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
