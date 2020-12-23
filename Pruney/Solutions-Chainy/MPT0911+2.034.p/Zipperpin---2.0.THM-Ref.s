%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZL9MMcOI1s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:00 EST 2020

% Result     : Theorem 47.72s
% Output     : Refutation 47.72s
% Verified   : 
% Statistics : Number of formulae       :  183 (1109 expanded)
%              Number of leaves         :   33 ( 350 expanded)
%              Depth                    :   24
%              Number of atoms          : 1694 (13948 expanded)
%              Number of equality atoms :  186 (1414 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('0',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_zfmisc_1 @ X13 @ X14 @ X15 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) @ X15 ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) )
        = X9 )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
        = X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
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
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('5',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_zfmisc_1 @ X13 @ X14 @ X15 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('7',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X16 ) @ X18 )
      | ~ ( r2_hidden @ X16 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf(fc11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X5: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X5 ) )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ( ( k2_relat_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C ) ),
    inference('sup+',[status(thm)],['2','13'])).

thf('15',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['15','16'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('18',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X1 @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('19',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
        = X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('21',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t23_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( A
          = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ) )).

thf('22',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19
        = ( k4_tarski @ ( k1_mcart_1 @ X19 ) @ ( k2_mcart_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X20 )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('23',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_zfmisc_1 @ X13 @ X14 @ X15 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('25',plain,(
    ! [X6: $i,X7: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( v1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('29',plain,
    ( ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
    | ( ( k2_relat_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference('sup+',[status(thm)],['20','29'])).

thf('31',plain,
    ( ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('35',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_zfmisc_1 @ X13 @ X14 @ X15 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('36',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X16 ) @ X17 )
      | ~ ( r2_hidden @ X16 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X16 ) @ X17 )
      | ~ ( r2_hidden @ X16 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('42',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X1 @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('44',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('46',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19
        = ( k4_tarski @ ( k1_mcart_1 @ X19 ) @ ( k2_mcart_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X20 )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('47',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X6: $i,X7: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('49',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('50',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_mcart_1 @ X10 @ X11 @ X12 )
      = ( k4_tarski @ ( k4_tarski @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X0 )
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('53',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X16 ) @ X18 )
      | ~ ( r2_hidden @ X16 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('54',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('56',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X1 @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('58',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ sk_B )
      | ( sk_E
       != ( k3_mcart_1 @ X26 @ X25 @ X27 ) )
      | ( sk_D = X27 )
      | ~ ( m1_subset_1 @ X27 @ sk_C )
      | ~ ( m1_subset_1 @ X26 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_D = X1 )
      | ( sk_E
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ( sk_D = X0 )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
      | ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( sk_E != sk_E )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) )
    | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['33','63'])).

thf('65',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    sk_D
 != ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
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

thf('68',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X21 @ X22 @ X24 @ X23 )
        = ( k2_mcart_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k3_zfmisc_1 @ X21 @ X22 @ X24 ) )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('69',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k2_mcart_1 @ sk_E ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['69','70','71','72'])).

thf('74',plain,(
    sk_D
 != ( k2_mcart_1 @ sk_E ) ),
    inference(demod,[status(thm)],['66','73'])).

thf('75',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['65','74'])).

thf('76',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 )
    | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','75'])).

thf('77',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('79',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
        = X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('81',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_C )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('84',plain,(
    ! [X5: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X5 ) )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,
    ( ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
    | ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['82','86'])).

thf('88',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('90',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
    | ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X1 @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('92',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X0 )
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('94',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('96',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B )
    | ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X1 @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('98',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ sk_B )
      | ( sk_E
       != ( k3_mcart_1 @ X26 @ X25 @ X27 ) )
      | ( sk_D = X27 )
      | ~ ( m1_subset_1 @ X27 @ sk_C )
      | ~ ( m1_subset_1 @ X26 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_D = X1 )
      | ( sk_E
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['93','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ( sk_D = X0 )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
      | ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['92','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,
    ( ( sk_E != sk_E )
    | ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) )
    | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['87','103'])).

thf('105',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    sk_D
 != ( k2_mcart_1 @ sk_E ) ),
    inference(demod,[status(thm)],['66','73'])).

thf('107',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('109',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('112',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X1 @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('114',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['109','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('117',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( k1_xboole_0 = sk_C )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['81','117'])).

thf('119',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( k1_xboole_0 = sk_C ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('123',plain,(
    ! [X5: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X5 ) )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_relat_1 @ ( k2_relat_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['122','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k2_relat_1 @ ( k2_relat_1 @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['130','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ ( k2_relat_1 @ k1_xboole_0 ) ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['134'])).

thf('136',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) )
        = X9 )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k2_relat_1 @ ( k2_relat_1 @ k1_xboole_0 ) ) )
        = X0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['115','116'])).

thf('139',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['115','116'])).

thf('140',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['115','116'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['137','138','139','140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( k1_xboole_0 = X0 ) ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0 = sk_B )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['121','142'])).

thf('144',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['109','114'])).

thf('145',plain,
    ( ( k1_xboole_0 = sk_B )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['145','146','147'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZL9MMcOI1s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:48:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.18/0.34  % Number of cores: 8
% 0.18/0.34  % Python version: Python 3.6.8
% 0.18/0.34  % Running in FO mode
% 47.72/47.96  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 47.72/47.96  % Solved by: fo/fo7.sh
% 47.72/47.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 47.72/47.96  % done 67587 iterations in 47.493s
% 47.72/47.96  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 47.72/47.96  % SZS output start Refutation
% 47.72/47.96  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 47.72/47.96  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 47.72/47.96  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 47.72/47.96  thf(sk_C_type, type, sk_C: $i).
% 47.72/47.96  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 47.72/47.96  thf(sk_D_type, type, sk_D: $i).
% 47.72/47.96  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 47.72/47.96  thf(sk_E_type, type, sk_E: $i).
% 47.72/47.96  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 47.72/47.96  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 47.72/47.96  thf(sk_A_type, type, sk_A: $i).
% 47.72/47.96  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 47.72/47.96  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 47.72/47.96  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 47.72/47.96  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 47.72/47.96  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 47.72/47.96  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 47.72/47.96  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 47.72/47.96  thf(sk_B_type, type, sk_B: $i).
% 47.72/47.96  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 47.72/47.96  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 47.72/47.96  thf(d3_zfmisc_1, axiom,
% 47.72/47.96    (![A:$i,B:$i,C:$i]:
% 47.72/47.96     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 47.72/47.96       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 47.72/47.96  thf('0', plain,
% 47.72/47.96      (![X13 : $i, X14 : $i, X15 : $i]:
% 47.72/47.96         ((k3_zfmisc_1 @ X13 @ X14 @ X15)
% 47.72/47.96           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14) @ X15))),
% 47.72/47.96      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 47.72/47.96  thf(t195_relat_1, axiom,
% 47.72/47.96    (![A:$i,B:$i]:
% 47.72/47.96     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 47.72/47.96          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 47.72/47.96               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 47.72/47.96  thf('1', plain,
% 47.72/47.96      (![X8 : $i, X9 : $i]:
% 47.72/47.96         (((X8) = (k1_xboole_0))
% 47.72/47.96          | ((k2_relat_1 @ (k2_zfmisc_1 @ X8 @ X9)) = (X9))
% 47.72/47.96          | ((X9) = (k1_xboole_0)))),
% 47.72/47.96      inference('cnf', [status(esa)], [t195_relat_1])).
% 47.72/47.96  thf('2', plain,
% 47.72/47.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.72/47.96         (((k2_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0)) = (X0))
% 47.72/47.96          | ((X0) = (k1_xboole_0))
% 47.72/47.96          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0)))),
% 47.72/47.96      inference('sup+', [status(thm)], ['0', '1'])).
% 47.72/47.96  thf(t71_mcart_1, conjecture,
% 47.72/47.96    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 47.72/47.96     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 47.72/47.96       ( ( ![F:$i]:
% 47.72/47.96           ( ( m1_subset_1 @ F @ A ) =>
% 47.72/47.96             ( ![G:$i]:
% 47.72/47.96               ( ( m1_subset_1 @ G @ B ) =>
% 47.72/47.96                 ( ![H:$i]:
% 47.72/47.96                   ( ( m1_subset_1 @ H @ C ) =>
% 47.72/47.96                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 47.72/47.96                       ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 47.72/47.96         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 47.72/47.96           ( ( C ) = ( k1_xboole_0 ) ) | 
% 47.72/47.96           ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 47.72/47.96  thf(zf_stmt_0, negated_conjecture,
% 47.72/47.96    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 47.72/47.97        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 47.72/47.97          ( ( ![F:$i]:
% 47.72/47.97              ( ( m1_subset_1 @ F @ A ) =>
% 47.72/47.97                ( ![G:$i]:
% 47.72/47.97                  ( ( m1_subset_1 @ G @ B ) =>
% 47.72/47.97                    ( ![H:$i]:
% 47.72/47.97                      ( ( m1_subset_1 @ H @ C ) =>
% 47.72/47.97                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 47.72/47.97                          ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 47.72/47.97            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 47.72/47.97              ( ( C ) = ( k1_xboole_0 ) ) | 
% 47.72/47.97              ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 47.72/47.97    inference('cnf.neg', [status(esa)], [t71_mcart_1])).
% 47.72/47.97  thf('3', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 47.72/47.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.72/47.97  thf(t2_subset, axiom,
% 47.72/47.97    (![A:$i,B:$i]:
% 47.72/47.97     ( ( m1_subset_1 @ A @ B ) =>
% 47.72/47.97       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 47.72/47.97  thf('4', plain,
% 47.72/47.97      (![X3 : $i, X4 : $i]:
% 47.72/47.97         ((r2_hidden @ X3 @ X4)
% 47.72/47.97          | (v1_xboole_0 @ X4)
% 47.72/47.97          | ~ (m1_subset_1 @ X3 @ X4))),
% 47.72/47.97      inference('cnf', [status(esa)], [t2_subset])).
% 47.72/47.97  thf('5', plain,
% 47.72/47.97      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 47.72/47.97        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 47.72/47.97      inference('sup-', [status(thm)], ['3', '4'])).
% 47.72/47.97  thf('6', plain,
% 47.72/47.97      (![X13 : $i, X14 : $i, X15 : $i]:
% 47.72/47.97         ((k3_zfmisc_1 @ X13 @ X14 @ X15)
% 47.72/47.97           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14) @ X15))),
% 47.72/47.97      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 47.72/47.97  thf(t10_mcart_1, axiom,
% 47.72/47.97    (![A:$i,B:$i,C:$i]:
% 47.72/47.97     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 47.72/47.97       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 47.72/47.97         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 47.72/47.97  thf('7', plain,
% 47.72/47.97      (![X16 : $i, X17 : $i, X18 : $i]:
% 47.72/47.97         ((r2_hidden @ (k2_mcart_1 @ X16) @ X18)
% 47.72/47.97          | ~ (r2_hidden @ X16 @ (k2_zfmisc_1 @ X17 @ X18)))),
% 47.72/47.97      inference('cnf', [status(esa)], [t10_mcart_1])).
% 47.72/47.97  thf('8', plain,
% 47.72/47.97      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 47.72/47.97         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 47.72/47.97          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 47.72/47.97      inference('sup-', [status(thm)], ['6', '7'])).
% 47.72/47.97  thf('9', plain,
% 47.72/47.97      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 47.72/47.97        | (r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C))),
% 47.72/47.97      inference('sup-', [status(thm)], ['5', '8'])).
% 47.72/47.97  thf(fc11_relat_1, axiom,
% 47.72/47.97    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ))).
% 47.72/47.97  thf('10', plain,
% 47.72/47.97      (![X5 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X5)) | ~ (v1_xboole_0 @ X5))),
% 47.72/47.97      inference('cnf', [status(esa)], [fc11_relat_1])).
% 47.72/47.97  thf(l13_xboole_0, axiom,
% 47.72/47.97    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 47.72/47.97  thf('11', plain,
% 47.72/47.97      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 47.72/47.97      inference('cnf', [status(esa)], [l13_xboole_0])).
% 47.72/47.97  thf('12', plain,
% 47.72/47.97      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 47.72/47.97      inference('sup-', [status(thm)], ['10', '11'])).
% 47.72/47.97  thf('13', plain,
% 47.72/47.97      (((r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C)
% 47.72/47.97        | ((k2_relat_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 47.72/47.97      inference('sup-', [status(thm)], ['9', '12'])).
% 47.72/47.97  thf('14', plain,
% 47.72/47.97      ((((sk_C) = (k1_xboole_0))
% 47.72/47.97        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 47.72/47.97        | ((sk_C) = (k1_xboole_0))
% 47.72/47.97        | (r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C))),
% 47.72/47.97      inference('sup+', [status(thm)], ['2', '13'])).
% 47.72/47.97  thf('15', plain,
% 47.72/47.97      (((r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C)
% 47.72/47.97        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 47.72/47.97        | ((sk_C) = (k1_xboole_0)))),
% 47.72/47.97      inference('simplify', [status(thm)], ['14'])).
% 47.72/47.97  thf('16', plain, (((sk_C) != (k1_xboole_0))),
% 47.72/47.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.72/47.97  thf('17', plain,
% 47.72/47.97      (((r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C)
% 47.72/47.97        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 47.72/47.97      inference('simplify_reflect-', [status(thm)], ['15', '16'])).
% 47.72/47.97  thf(t1_subset, axiom,
% 47.72/47.97    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 47.72/47.97  thf('18', plain,
% 47.72/47.97      (![X1 : $i, X2 : $i]: ((m1_subset_1 @ X1 @ X2) | ~ (r2_hidden @ X1 @ X2))),
% 47.72/47.97      inference('cnf', [status(esa)], [t1_subset])).
% 47.72/47.97  thf('19', plain,
% 47.72/47.97      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 47.72/47.97        | (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C))),
% 47.72/47.97      inference('sup-', [status(thm)], ['17', '18'])).
% 47.72/47.97  thf('20', plain,
% 47.72/47.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.72/47.97         (((k2_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0)) = (X0))
% 47.72/47.97          | ((X0) = (k1_xboole_0))
% 47.72/47.97          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0)))),
% 47.72/47.97      inference('sup+', [status(thm)], ['0', '1'])).
% 47.72/47.97  thf('21', plain,
% 47.72/47.97      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 47.72/47.97        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 47.72/47.97      inference('sup-', [status(thm)], ['3', '4'])).
% 47.72/47.97  thf(t23_mcart_1, axiom,
% 47.72/47.97    (![A:$i,B:$i]:
% 47.72/47.97     ( ( v1_relat_1 @ B ) =>
% 47.72/47.97       ( ( r2_hidden @ A @ B ) =>
% 47.72/47.97         ( ( A ) = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ))).
% 47.72/47.97  thf('22', plain,
% 47.72/47.97      (![X19 : $i, X20 : $i]:
% 47.72/47.97         (((X19) = (k4_tarski @ (k1_mcart_1 @ X19) @ (k2_mcart_1 @ X19)))
% 47.72/47.97          | ~ (v1_relat_1 @ X20)
% 47.72/47.97          | ~ (r2_hidden @ X19 @ X20))),
% 47.72/47.97      inference('cnf', [status(esa)], [t23_mcart_1])).
% 47.72/47.97  thf('23', plain,
% 47.72/47.97      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 47.72/47.97        | ~ (v1_relat_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 47.72/47.97        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 47.72/47.97      inference('sup-', [status(thm)], ['21', '22'])).
% 47.72/47.97  thf('24', plain,
% 47.72/47.97      (![X13 : $i, X14 : $i, X15 : $i]:
% 47.72/47.97         ((k3_zfmisc_1 @ X13 @ X14 @ X15)
% 47.72/47.97           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14) @ X15))),
% 47.72/47.97      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 47.72/47.97  thf(fc6_relat_1, axiom,
% 47.72/47.97    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 47.72/47.97  thf('25', plain,
% 47.72/47.97      (![X6 : $i, X7 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X6 @ X7))),
% 47.72/47.97      inference('cnf', [status(esa)], [fc6_relat_1])).
% 47.72/47.97  thf('26', plain,
% 47.72/47.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.72/47.97         (v1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))),
% 47.72/47.97      inference('sup+', [status(thm)], ['24', '25'])).
% 47.72/47.97  thf('27', plain,
% 47.72/47.97      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 47.72/47.97        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 47.72/47.97      inference('demod', [status(thm)], ['23', '26'])).
% 47.72/47.97  thf('28', plain,
% 47.72/47.97      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 47.72/47.97      inference('sup-', [status(thm)], ['10', '11'])).
% 47.72/47.97  thf('29', plain,
% 47.72/47.97      ((((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 47.72/47.97        | ((k2_relat_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 47.72/47.97      inference('sup-', [status(thm)], ['27', '28'])).
% 47.72/47.97  thf('30', plain,
% 47.72/47.97      ((((sk_C) = (k1_xboole_0))
% 47.72/47.97        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 47.72/47.97        | ((sk_C) = (k1_xboole_0))
% 47.72/47.97        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 47.72/47.97      inference('sup+', [status(thm)], ['20', '29'])).
% 47.72/47.97  thf('31', plain,
% 47.72/47.97      ((((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 47.72/47.97        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 47.72/47.97        | ((sk_C) = (k1_xboole_0)))),
% 47.72/47.97      inference('simplify', [status(thm)], ['30'])).
% 47.72/47.97  thf('32', plain, (((sk_C) != (k1_xboole_0))),
% 47.72/47.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.72/47.97  thf('33', plain,
% 47.72/47.97      ((((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 47.72/47.97        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 47.72/47.97      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 47.72/47.97  thf('34', plain,
% 47.72/47.97      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 47.72/47.97        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 47.72/47.97      inference('sup-', [status(thm)], ['3', '4'])).
% 47.72/47.97  thf('35', plain,
% 47.72/47.97      (![X13 : $i, X14 : $i, X15 : $i]:
% 47.72/47.97         ((k3_zfmisc_1 @ X13 @ X14 @ X15)
% 47.72/47.97           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14) @ X15))),
% 47.72/47.97      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 47.72/47.97  thf('36', plain,
% 47.72/47.97      (![X16 : $i, X17 : $i, X18 : $i]:
% 47.72/47.97         ((r2_hidden @ (k1_mcart_1 @ X16) @ X17)
% 47.72/47.97          | ~ (r2_hidden @ X16 @ (k2_zfmisc_1 @ X17 @ X18)))),
% 47.72/47.97      inference('cnf', [status(esa)], [t10_mcart_1])).
% 47.72/47.97  thf('37', plain,
% 47.72/47.97      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 47.72/47.97         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 47.72/47.97          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 47.72/47.97      inference('sup-', [status(thm)], ['35', '36'])).
% 47.72/47.97  thf('38', plain,
% 47.72/47.97      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 47.72/47.97        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 47.72/47.97      inference('sup-', [status(thm)], ['34', '37'])).
% 47.72/47.97  thf('39', plain,
% 47.72/47.97      (![X16 : $i, X17 : $i, X18 : $i]:
% 47.72/47.97         ((r2_hidden @ (k1_mcart_1 @ X16) @ X17)
% 47.72/47.97          | ~ (r2_hidden @ X16 @ (k2_zfmisc_1 @ X17 @ X18)))),
% 47.72/47.97      inference('cnf', [status(esa)], [t10_mcart_1])).
% 47.72/47.97  thf('40', plain,
% 47.72/47.97      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 47.72/47.97        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 47.72/47.97      inference('sup-', [status(thm)], ['38', '39'])).
% 47.72/47.97  thf('41', plain,
% 47.72/47.97      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 47.72/47.97      inference('cnf', [status(esa)], [l13_xboole_0])).
% 47.72/47.97  thf('42', plain,
% 47.72/47.97      (((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 47.72/47.97        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 47.72/47.97      inference('sup-', [status(thm)], ['40', '41'])).
% 47.72/47.97  thf('43', plain,
% 47.72/47.97      (![X1 : $i, X2 : $i]: ((m1_subset_1 @ X1 @ X2) | ~ (r2_hidden @ X1 @ X2))),
% 47.72/47.97      inference('cnf', [status(esa)], [t1_subset])).
% 47.72/47.97  thf('44', plain,
% 47.72/47.97      ((((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))
% 47.72/47.97        | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 47.72/47.97      inference('sup-', [status(thm)], ['42', '43'])).
% 47.72/47.97  thf('45', plain,
% 47.72/47.97      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 47.72/47.97        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 47.72/47.97      inference('sup-', [status(thm)], ['34', '37'])).
% 47.72/47.97  thf('46', plain,
% 47.72/47.97      (![X19 : $i, X20 : $i]:
% 47.72/47.97         (((X19) = (k4_tarski @ (k1_mcart_1 @ X19) @ (k2_mcart_1 @ X19)))
% 47.72/47.97          | ~ (v1_relat_1 @ X20)
% 47.72/47.97          | ~ (r2_hidden @ X19 @ X20))),
% 47.72/47.97      inference('cnf', [status(esa)], [t23_mcart_1])).
% 47.72/47.97  thf('47', plain,
% 47.72/47.97      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 47.72/47.97        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 47.72/47.97        | ((k1_mcart_1 @ sk_E)
% 47.72/47.97            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 47.72/47.97               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 47.72/47.97      inference('sup-', [status(thm)], ['45', '46'])).
% 47.72/47.97  thf('48', plain,
% 47.72/47.97      (![X6 : $i, X7 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X6 @ X7))),
% 47.72/47.97      inference('cnf', [status(esa)], [fc6_relat_1])).
% 47.72/47.97  thf('49', plain,
% 47.72/47.97      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 47.72/47.97        | ((k1_mcart_1 @ sk_E)
% 47.72/47.97            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 47.72/47.97               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 47.72/47.97      inference('demod', [status(thm)], ['47', '48'])).
% 47.72/47.97  thf(d3_mcart_1, axiom,
% 47.72/47.97    (![A:$i,B:$i,C:$i]:
% 47.72/47.97     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 47.72/47.97  thf('50', plain,
% 47.72/47.97      (![X10 : $i, X11 : $i, X12 : $i]:
% 47.72/47.97         ((k3_mcart_1 @ X10 @ X11 @ X12)
% 47.72/47.97           = (k4_tarski @ (k4_tarski @ X10 @ X11) @ X12))),
% 47.72/47.97      inference('cnf', [status(esa)], [d3_mcart_1])).
% 47.72/47.97  thf('51', plain,
% 47.72/47.97      (![X0 : $i]:
% 47.72/47.97         (((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 47.72/47.97            (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X0)
% 47.72/47.97            = (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 47.72/47.97          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 47.72/47.97      inference('sup+', [status(thm)], ['49', '50'])).
% 47.72/47.97  thf('52', plain,
% 47.72/47.97      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 47.72/47.97        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 47.72/47.97      inference('sup-', [status(thm)], ['34', '37'])).
% 47.72/47.97  thf('53', plain,
% 47.72/47.97      (![X16 : $i, X17 : $i, X18 : $i]:
% 47.72/47.97         ((r2_hidden @ (k2_mcart_1 @ X16) @ X18)
% 47.72/47.97          | ~ (r2_hidden @ X16 @ (k2_zfmisc_1 @ X17 @ X18)))),
% 47.72/47.97      inference('cnf', [status(esa)], [t10_mcart_1])).
% 47.72/47.97  thf('54', plain,
% 47.72/47.97      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 47.72/47.97        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B))),
% 47.72/47.97      inference('sup-', [status(thm)], ['52', '53'])).
% 47.72/47.97  thf('55', plain,
% 47.72/47.97      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 47.72/47.97      inference('cnf', [status(esa)], [l13_xboole_0])).
% 47.72/47.97  thf('56', plain,
% 47.72/47.97      (((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B)
% 47.72/47.97        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 47.72/47.97      inference('sup-', [status(thm)], ['54', '55'])).
% 47.72/47.97  thf('57', plain,
% 47.72/47.97      (![X1 : $i, X2 : $i]: ((m1_subset_1 @ X1 @ X2) | ~ (r2_hidden @ X1 @ X2))),
% 47.72/47.97      inference('cnf', [status(esa)], [t1_subset])).
% 47.72/47.97  thf('58', plain,
% 47.72/47.97      ((((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))
% 47.72/47.97        | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B))),
% 47.72/47.97      inference('sup-', [status(thm)], ['56', '57'])).
% 47.72/47.97  thf('59', plain,
% 47.72/47.97      (![X25 : $i, X26 : $i, X27 : $i]:
% 47.72/47.97         (~ (m1_subset_1 @ X25 @ sk_B)
% 47.72/47.97          | ((sk_E) != (k3_mcart_1 @ X26 @ X25 @ X27))
% 47.72/47.97          | ((sk_D) = (X27))
% 47.72/47.97          | ~ (m1_subset_1 @ X27 @ sk_C)
% 47.72/47.97          | ~ (m1_subset_1 @ X26 @ sk_A))),
% 47.72/47.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.72/47.97  thf('60', plain,
% 47.72/47.97      (![X0 : $i, X1 : $i]:
% 47.72/47.97         (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))
% 47.72/47.97          | ~ (m1_subset_1 @ X0 @ sk_A)
% 47.72/47.97          | ~ (m1_subset_1 @ X1 @ sk_C)
% 47.72/47.97          | ((sk_D) = (X1))
% 47.72/47.97          | ((sk_E)
% 47.72/47.97              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1)))),
% 47.72/47.97      inference('sup-', [status(thm)], ['58', '59'])).
% 47.72/47.97  thf('61', plain,
% 47.72/47.97      (![X0 : $i]:
% 47.72/47.97         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 47.72/47.97          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 47.72/47.97          | ((sk_D) = (X0))
% 47.72/47.97          | ~ (m1_subset_1 @ X0 @ sk_C)
% 47.72/47.97          | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 47.72/47.97          | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 47.72/47.97      inference('sup-', [status(thm)], ['51', '60'])).
% 47.72/47.97  thf('62', plain,
% 47.72/47.97      (![X0 : $i]:
% 47.72/47.97         (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))
% 47.72/47.97          | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))
% 47.72/47.97          | ~ (m1_subset_1 @ X0 @ sk_C)
% 47.72/47.97          | ((sk_D) = (X0))
% 47.72/47.97          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 47.72/47.97          | ((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0)))),
% 47.72/47.97      inference('sup-', [status(thm)], ['44', '61'])).
% 47.72/47.97  thf('63', plain,
% 47.72/47.97      (![X0 : $i]:
% 47.72/47.97         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 47.72/47.97          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 47.72/47.97          | ((sk_D) = (X0))
% 47.72/47.97          | ~ (m1_subset_1 @ X0 @ sk_C)
% 47.72/47.97          | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 47.72/47.97      inference('simplify', [status(thm)], ['62'])).
% 47.72/47.97  thf('64', plain,
% 47.72/47.97      ((((sk_E) != (sk_E))
% 47.72/47.97        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 47.72/47.97        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))
% 47.72/47.97        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)
% 47.72/47.97        | ((sk_D) = (k2_mcart_1 @ sk_E))
% 47.72/47.97        | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 47.72/47.97      inference('sup-', [status(thm)], ['33', '63'])).
% 47.72/47.97  thf('65', plain,
% 47.72/47.97      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 47.72/47.97        | ((sk_D) = (k2_mcart_1 @ sk_E))
% 47.72/47.97        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)
% 47.72/47.97        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))
% 47.72/47.97        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 47.72/47.97      inference('simplify', [status(thm)], ['64'])).
% 47.72/47.97  thf('66', plain, (((sk_D) != (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E))),
% 47.72/47.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.72/47.97  thf('67', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 47.72/47.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.72/47.97  thf(t50_mcart_1, axiom,
% 47.72/47.97    (![A:$i,B:$i,C:$i]:
% 47.72/47.97     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 47.72/47.97          ( ( C ) != ( k1_xboole_0 ) ) & 
% 47.72/47.97          ( ~( ![D:$i]:
% 47.72/47.97               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 47.72/47.97                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 47.72/47.97                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 47.72/47.97                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 47.72/47.97                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 47.72/47.97                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 47.72/47.97  thf('68', plain,
% 47.72/47.97      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 47.72/47.97         (((X21) = (k1_xboole_0))
% 47.72/47.97          | ((X22) = (k1_xboole_0))
% 47.72/47.97          | ((k7_mcart_1 @ X21 @ X22 @ X24 @ X23) = (k2_mcart_1 @ X23))
% 47.72/47.97          | ~ (m1_subset_1 @ X23 @ (k3_zfmisc_1 @ X21 @ X22 @ X24))
% 47.72/47.97          | ((X24) = (k1_xboole_0)))),
% 47.72/47.97      inference('cnf', [status(esa)], [t50_mcart_1])).
% 47.72/47.97  thf('69', plain,
% 47.72/47.97      ((((sk_C) = (k1_xboole_0))
% 47.72/47.97        | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))
% 47.72/47.97        | ((sk_B) = (k1_xboole_0))
% 47.72/47.97        | ((sk_A) = (k1_xboole_0)))),
% 47.72/47.97      inference('sup-', [status(thm)], ['67', '68'])).
% 47.72/47.97  thf('70', plain, (((sk_A) != (k1_xboole_0))),
% 47.72/47.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.72/47.97  thf('71', plain, (((sk_B) != (k1_xboole_0))),
% 47.72/47.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.72/47.97  thf('72', plain, (((sk_C) != (k1_xboole_0))),
% 47.72/47.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.72/47.97  thf('73', plain,
% 47.72/47.97      (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))),
% 47.72/47.97      inference('simplify_reflect-', [status(thm)], ['69', '70', '71', '72'])).
% 47.72/47.97  thf('74', plain, (((sk_D) != (k2_mcart_1 @ sk_E))),
% 47.72/47.97      inference('demod', [status(thm)], ['66', '73'])).
% 47.72/47.97  thf('75', plain,
% 47.72/47.97      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 47.72/47.97        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)
% 47.72/47.97        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))
% 47.72/47.97        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 47.72/47.97      inference('simplify_reflect-', [status(thm)], ['65', '74'])).
% 47.72/47.97  thf('76', plain,
% 47.72/47.97      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 47.72/47.97        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 47.72/47.97        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))
% 47.72/47.97        | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 47.72/47.97      inference('sup-', [status(thm)], ['19', '75'])).
% 47.72/47.97  thf('77', plain,
% 47.72/47.97      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 47.72/47.97        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0))
% 47.72/47.97        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 47.72/47.97      inference('simplify', [status(thm)], ['76'])).
% 47.72/47.97  thf('78', plain,
% 47.72/47.97      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 47.72/47.97      inference('cnf', [status(esa)], [l13_xboole_0])).
% 47.72/47.97  thf('79', plain,
% 47.72/47.97      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 47.72/47.97        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 47.72/47.97      inference('clc', [status(thm)], ['77', '78'])).
% 47.72/47.97  thf('80', plain,
% 47.72/47.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.72/47.97         (((k2_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0)) = (X0))
% 47.72/47.97          | ((X0) = (k1_xboole_0))
% 47.72/47.97          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0)))),
% 47.72/47.97      inference('sup+', [status(thm)], ['0', '1'])).
% 47.72/47.97  thf('81', plain,
% 47.72/47.97      ((((k2_relat_1 @ k1_xboole_0) = (sk_C))
% 47.72/47.97        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 47.72/47.97        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 47.72/47.97        | ((sk_C) = (k1_xboole_0)))),
% 47.72/47.97      inference('sup+', [status(thm)], ['79', '80'])).
% 47.72/47.97  thf('82', plain,
% 47.72/47.97      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 47.72/47.97        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 47.72/47.97      inference('demod', [status(thm)], ['23', '26'])).
% 47.72/47.97  thf('83', plain,
% 47.72/47.97      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 47.72/47.97      inference('sup-', [status(thm)], ['10', '11'])).
% 47.72/47.97  thf('84', plain,
% 47.72/47.97      (![X5 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X5)) | ~ (v1_xboole_0 @ X5))),
% 47.72/47.97      inference('cnf', [status(esa)], [fc11_relat_1])).
% 47.72/47.97  thf('85', plain,
% 47.72/47.97      (![X0 : $i]:
% 47.72/47.97         ((v1_xboole_0 @ k1_xboole_0)
% 47.72/47.97          | ~ (v1_xboole_0 @ X0)
% 47.72/47.97          | ~ (v1_xboole_0 @ X0))),
% 47.72/47.97      inference('sup+', [status(thm)], ['83', '84'])).
% 47.72/47.97  thf('86', plain,
% 47.72/47.97      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ k1_xboole_0))),
% 47.72/47.97      inference('simplify', [status(thm)], ['85'])).
% 47.72/47.97  thf('87', plain,
% 47.72/47.97      ((((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 47.72/47.97        | (v1_xboole_0 @ k1_xboole_0))),
% 47.72/47.97      inference('sup-', [status(thm)], ['82', '86'])).
% 47.72/47.97  thf('88', plain,
% 47.72/47.97      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 47.72/47.97        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 47.72/47.97      inference('sup-', [status(thm)], ['38', '39'])).
% 47.72/47.97  thf('89', plain,
% 47.72/47.97      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ k1_xboole_0))),
% 47.72/47.97      inference('simplify', [status(thm)], ['85'])).
% 47.72/47.97  thf('90', plain,
% 47.72/47.97      (((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 47.72/47.97        | (v1_xboole_0 @ k1_xboole_0))),
% 47.72/47.97      inference('sup-', [status(thm)], ['88', '89'])).
% 47.72/47.97  thf('91', plain,
% 47.72/47.97      (![X1 : $i, X2 : $i]: ((m1_subset_1 @ X1 @ X2) | ~ (r2_hidden @ X1 @ X2))),
% 47.72/47.97      inference('cnf', [status(esa)], [t1_subset])).
% 47.72/47.97  thf('92', plain,
% 47.72/47.97      (((v1_xboole_0 @ k1_xboole_0)
% 47.72/47.97        | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 47.72/47.97      inference('sup-', [status(thm)], ['90', '91'])).
% 47.72/47.97  thf('93', plain,
% 47.72/47.97      (![X0 : $i]:
% 47.72/47.97         (((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 47.72/47.97            (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X0)
% 47.72/47.97            = (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 47.72/47.97          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 47.72/47.97      inference('sup+', [status(thm)], ['49', '50'])).
% 47.72/47.97  thf('94', plain,
% 47.72/47.97      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 47.72/47.97        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B))),
% 47.72/47.97      inference('sup-', [status(thm)], ['52', '53'])).
% 47.72/47.97  thf('95', plain,
% 47.72/47.97      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ k1_xboole_0))),
% 47.72/47.97      inference('simplify', [status(thm)], ['85'])).
% 47.72/47.97  thf('96', plain,
% 47.72/47.97      (((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B)
% 47.72/47.97        | (v1_xboole_0 @ k1_xboole_0))),
% 47.72/47.97      inference('sup-', [status(thm)], ['94', '95'])).
% 47.72/47.97  thf('97', plain,
% 47.72/47.97      (![X1 : $i, X2 : $i]: ((m1_subset_1 @ X1 @ X2) | ~ (r2_hidden @ X1 @ X2))),
% 47.72/47.97      inference('cnf', [status(esa)], [t1_subset])).
% 47.72/47.97  thf('98', plain,
% 47.72/47.97      (((v1_xboole_0 @ k1_xboole_0)
% 47.72/47.97        | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B))),
% 47.72/47.97      inference('sup-', [status(thm)], ['96', '97'])).
% 47.72/47.97  thf('99', plain,
% 47.72/47.97      (![X25 : $i, X26 : $i, X27 : $i]:
% 47.72/47.97         (~ (m1_subset_1 @ X25 @ sk_B)
% 47.72/47.97          | ((sk_E) != (k3_mcart_1 @ X26 @ X25 @ X27))
% 47.72/47.97          | ((sk_D) = (X27))
% 47.72/47.97          | ~ (m1_subset_1 @ X27 @ sk_C)
% 47.72/47.97          | ~ (m1_subset_1 @ X26 @ sk_A))),
% 47.72/47.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.72/47.97  thf('100', plain,
% 47.72/47.97      (![X0 : $i, X1 : $i]:
% 47.72/47.97         ((v1_xboole_0 @ k1_xboole_0)
% 47.72/47.97          | ~ (m1_subset_1 @ X0 @ sk_A)
% 47.72/47.97          | ~ (m1_subset_1 @ X1 @ sk_C)
% 47.72/47.97          | ((sk_D) = (X1))
% 47.72/47.97          | ((sk_E)
% 47.72/47.97              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1)))),
% 47.72/47.97      inference('sup-', [status(thm)], ['98', '99'])).
% 47.72/47.97  thf('101', plain,
% 47.72/47.97      (![X0 : $i]:
% 47.72/47.97         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 47.72/47.97          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 47.72/47.97          | ((sk_D) = (X0))
% 47.72/47.97          | ~ (m1_subset_1 @ X0 @ sk_C)
% 47.72/47.97          | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 47.72/47.97          | (v1_xboole_0 @ k1_xboole_0))),
% 47.72/47.97      inference('sup-', [status(thm)], ['93', '100'])).
% 47.72/47.97  thf('102', plain,
% 47.72/47.97      (![X0 : $i]:
% 47.72/47.97         ((v1_xboole_0 @ k1_xboole_0)
% 47.72/47.97          | (v1_xboole_0 @ k1_xboole_0)
% 47.72/47.97          | ~ (m1_subset_1 @ X0 @ sk_C)
% 47.72/47.97          | ((sk_D) = (X0))
% 47.72/47.97          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 47.72/47.97          | ((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0)))),
% 47.72/47.97      inference('sup-', [status(thm)], ['92', '101'])).
% 47.72/47.97  thf('103', plain,
% 47.72/47.97      (![X0 : $i]:
% 47.72/47.97         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 47.72/47.97          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 47.72/47.97          | ((sk_D) = (X0))
% 47.72/47.97          | ~ (m1_subset_1 @ X0 @ sk_C)
% 47.72/47.97          | (v1_xboole_0 @ k1_xboole_0))),
% 47.72/47.97      inference('simplify', [status(thm)], ['102'])).
% 47.72/47.97  thf('104', plain,
% 47.72/47.97      ((((sk_E) != (sk_E))
% 47.72/47.97        | (v1_xboole_0 @ k1_xboole_0)
% 47.72/47.97        | (v1_xboole_0 @ k1_xboole_0)
% 47.72/47.97        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)
% 47.72/47.97        | ((sk_D) = (k2_mcart_1 @ sk_E))
% 47.72/47.97        | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 47.72/47.97      inference('sup-', [status(thm)], ['87', '103'])).
% 47.72/47.97  thf('105', plain,
% 47.72/47.97      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 47.72/47.97        | ((sk_D) = (k2_mcart_1 @ sk_E))
% 47.72/47.97        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)
% 47.72/47.97        | (v1_xboole_0 @ k1_xboole_0))),
% 47.72/47.97      inference('simplify', [status(thm)], ['104'])).
% 47.72/47.97  thf('106', plain, (((sk_D) != (k2_mcart_1 @ sk_E))),
% 47.72/47.97      inference('demod', [status(thm)], ['66', '73'])).
% 47.72/47.97  thf('107', plain,
% 47.72/47.97      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 47.72/47.97        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)
% 47.72/47.97        | (v1_xboole_0 @ k1_xboole_0))),
% 47.72/47.97      inference('simplify_reflect-', [status(thm)], ['105', '106'])).
% 47.72/47.97  thf('108', plain,
% 47.72/47.97      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ k1_xboole_0))),
% 47.72/47.97      inference('simplify', [status(thm)], ['85'])).
% 47.72/47.97  thf('109', plain,
% 47.72/47.97      (((v1_xboole_0 @ k1_xboole_0)
% 47.72/47.97        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C))),
% 47.72/47.97      inference('clc', [status(thm)], ['107', '108'])).
% 47.72/47.97  thf('110', plain,
% 47.72/47.97      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 47.72/47.97        | (r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C))),
% 47.72/47.97      inference('sup-', [status(thm)], ['5', '8'])).
% 47.72/47.97  thf('111', plain,
% 47.72/47.97      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ k1_xboole_0))),
% 47.72/47.97      inference('simplify', [status(thm)], ['85'])).
% 47.72/47.97  thf('112', plain,
% 47.72/47.97      (((r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C) | (v1_xboole_0 @ k1_xboole_0))),
% 47.72/47.97      inference('sup-', [status(thm)], ['110', '111'])).
% 47.72/47.97  thf('113', plain,
% 47.72/47.97      (![X1 : $i, X2 : $i]: ((m1_subset_1 @ X1 @ X2) | ~ (r2_hidden @ X1 @ X2))),
% 47.72/47.97      inference('cnf', [status(esa)], [t1_subset])).
% 47.72/47.97  thf('114', plain,
% 47.72/47.97      (((v1_xboole_0 @ k1_xboole_0)
% 47.72/47.97        | (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C))),
% 47.72/47.97      inference('sup-', [status(thm)], ['112', '113'])).
% 47.72/47.97  thf('115', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 47.72/47.97      inference('clc', [status(thm)], ['109', '114'])).
% 47.72/47.97  thf('116', plain,
% 47.72/47.97      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 47.72/47.97      inference('sup-', [status(thm)], ['10', '11'])).
% 47.72/47.97  thf('117', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 47.72/47.97      inference('sup-', [status(thm)], ['115', '116'])).
% 47.72/47.97  thf('118', plain,
% 47.72/47.97      ((((k1_xboole_0) = (sk_C))
% 47.72/47.97        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 47.72/47.97        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 47.72/47.97        | ((sk_C) = (k1_xboole_0)))),
% 47.72/47.97      inference('demod', [status(thm)], ['81', '117'])).
% 47.72/47.97  thf('119', plain,
% 47.72/47.97      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 47.72/47.97        | ((k1_xboole_0) = (sk_C)))),
% 47.72/47.97      inference('simplify', [status(thm)], ['118'])).
% 47.72/47.97  thf('120', plain, (((sk_C) != (k1_xboole_0))),
% 47.72/47.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.72/47.97  thf('121', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 47.72/47.97      inference('simplify_reflect-', [status(thm)], ['119', '120'])).
% 47.72/47.97  thf('122', plain,
% 47.72/47.97      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 47.72/47.97      inference('sup-', [status(thm)], ['10', '11'])).
% 47.72/47.97  thf('123', plain,
% 47.72/47.97      (![X5 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X5)) | ~ (v1_xboole_0 @ X5))),
% 47.72/47.97      inference('cnf', [status(esa)], [fc11_relat_1])).
% 47.72/47.97  thf('124', plain,
% 47.72/47.97      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 47.72/47.97      inference('sup-', [status(thm)], ['10', '11'])).
% 47.72/47.97  thf('125', plain,
% 47.72/47.97      (![X0 : $i]:
% 47.72/47.97         (~ (v1_xboole_0 @ X0)
% 47.72/47.97          | ((k2_relat_1 @ (k2_relat_1 @ X0)) = (k1_xboole_0)))),
% 47.72/47.97      inference('sup-', [status(thm)], ['123', '124'])).
% 47.72/47.97  thf('126', plain,
% 47.72/47.97      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ k1_xboole_0))),
% 47.72/47.97      inference('simplify', [status(thm)], ['85'])).
% 47.72/47.97  thf('127', plain,
% 47.72/47.97      (![X0 : $i, X1 : $i]:
% 47.72/47.97         ((v1_xboole_0 @ (k2_relat_1 @ (k2_relat_1 @ X0)))
% 47.72/47.97          | ~ (v1_xboole_0 @ X0)
% 47.72/47.97          | ~ (v1_xboole_0 @ X1))),
% 47.72/47.97      inference('sup+', [status(thm)], ['125', '126'])).
% 47.72/47.97  thf('128', plain,
% 47.72/47.97      (![X0 : $i]:
% 47.72/47.97         ((v1_xboole_0 @ (k2_relat_1 @ (k2_relat_1 @ X0)))
% 47.72/47.97          | ~ (v1_xboole_0 @ X0))),
% 47.72/47.97      inference('condensation', [status(thm)], ['127'])).
% 47.72/47.97  thf('129', plain,
% 47.72/47.97      (![X0 : $i]:
% 47.72/47.97         ((v1_xboole_0 @ (k2_relat_1 @ k1_xboole_0))
% 47.72/47.97          | ~ (v1_xboole_0 @ X0)
% 47.72/47.97          | ~ (v1_xboole_0 @ X0))),
% 47.72/47.97      inference('sup+', [status(thm)], ['122', '128'])).
% 47.72/47.97  thf('130', plain,
% 47.72/47.97      (![X0 : $i]:
% 47.72/47.97         (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k2_relat_1 @ k1_xboole_0)))),
% 47.72/47.97      inference('simplify', [status(thm)], ['129'])).
% 47.72/47.97  thf('131', plain,
% 47.72/47.97      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 47.72/47.97      inference('sup-', [status(thm)], ['10', '11'])).
% 47.72/47.97  thf('132', plain,
% 47.72/47.97      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 47.72/47.97      inference('cnf', [status(esa)], [l13_xboole_0])).
% 47.72/47.97  thf('133', plain,
% 47.72/47.97      (![X0 : $i, X1 : $i]:
% 47.72/47.97         (((X1) = (k2_relat_1 @ X0))
% 47.72/47.97          | ~ (v1_xboole_0 @ X0)
% 47.72/47.97          | ~ (v1_xboole_0 @ X1))),
% 47.72/47.97      inference('sup+', [status(thm)], ['131', '132'])).
% 47.72/47.97  thf('134', plain,
% 47.72/47.97      (![X0 : $i, X1 : $i]:
% 47.72/47.97         (~ (v1_xboole_0 @ X1)
% 47.72/47.97          | ~ (v1_xboole_0 @ X0)
% 47.72/47.97          | ((X0) = (k2_relat_1 @ (k2_relat_1 @ k1_xboole_0))))),
% 47.72/47.97      inference('sup-', [status(thm)], ['130', '133'])).
% 47.72/47.97  thf('135', plain,
% 47.72/47.97      (![X0 : $i]:
% 47.72/47.97         (((X0) = (k2_relat_1 @ (k2_relat_1 @ k1_xboole_0)))
% 47.72/47.97          | ~ (v1_xboole_0 @ X0))),
% 47.72/47.97      inference('condensation', [status(thm)], ['134'])).
% 47.72/47.97  thf('136', plain,
% 47.72/47.97      (![X8 : $i, X9 : $i]:
% 47.72/47.97         (((X8) = (k1_xboole_0))
% 47.72/47.97          | ((k2_relat_1 @ (k2_zfmisc_1 @ X8 @ X9)) = (X9))
% 47.72/47.97          | ((X9) = (k1_xboole_0)))),
% 47.72/47.97      inference('cnf', [status(esa)], [t195_relat_1])).
% 47.72/47.97  thf('137', plain,
% 47.72/47.97      (![X0 : $i, X1 : $i]:
% 47.72/47.97         (((k2_relat_1 @ (k2_relat_1 @ (k2_relat_1 @ k1_xboole_0))) = (X0))
% 47.72/47.97          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 47.72/47.97          | ((X0) = (k1_xboole_0))
% 47.72/47.97          | ((X1) = (k1_xboole_0)))),
% 47.72/47.97      inference('sup+', [status(thm)], ['135', '136'])).
% 47.72/47.97  thf('138', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 47.72/47.97      inference('sup-', [status(thm)], ['115', '116'])).
% 47.72/47.97  thf('139', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 47.72/47.97      inference('sup-', [status(thm)], ['115', '116'])).
% 47.72/47.97  thf('140', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 47.72/47.97      inference('sup-', [status(thm)], ['115', '116'])).
% 47.72/47.97  thf('141', plain,
% 47.72/47.97      (![X0 : $i, X1 : $i]:
% 47.72/47.97         (((k1_xboole_0) = (X0))
% 47.72/47.97          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 47.72/47.97          | ((X0) = (k1_xboole_0))
% 47.72/47.97          | ((X1) = (k1_xboole_0)))),
% 47.72/47.97      inference('demod', [status(thm)], ['137', '138', '139', '140'])).
% 47.72/47.97  thf('142', plain,
% 47.72/47.97      (![X0 : $i, X1 : $i]:
% 47.72/47.97         (((X1) = (k1_xboole_0))
% 47.72/47.97          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 47.72/47.97          | ((k1_xboole_0) = (X0)))),
% 47.72/47.97      inference('simplify', [status(thm)], ['141'])).
% 47.72/47.97  thf('143', plain,
% 47.72/47.97      ((~ (v1_xboole_0 @ k1_xboole_0)
% 47.72/47.97        | ((k1_xboole_0) = (sk_B))
% 47.72/47.97        | ((sk_A) = (k1_xboole_0)))),
% 47.72/47.97      inference('sup-', [status(thm)], ['121', '142'])).
% 47.72/47.97  thf('144', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 47.72/47.97      inference('clc', [status(thm)], ['109', '114'])).
% 47.72/47.97  thf('145', plain, ((((k1_xboole_0) = (sk_B)) | ((sk_A) = (k1_xboole_0)))),
% 47.72/47.97      inference('demod', [status(thm)], ['143', '144'])).
% 47.72/47.97  thf('146', plain, (((sk_A) != (k1_xboole_0))),
% 47.72/47.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.72/47.97  thf('147', plain, (((sk_B) != (k1_xboole_0))),
% 47.72/47.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.72/47.97  thf('148', plain, ($false),
% 47.72/47.97      inference('simplify_reflect-', [status(thm)], ['145', '146', '147'])).
% 47.72/47.97  
% 47.72/47.97  % SZS output end Refutation
% 47.72/47.97  
% 47.72/47.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
