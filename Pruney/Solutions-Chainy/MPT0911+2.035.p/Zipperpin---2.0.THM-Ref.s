%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0PX1bXh82i

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:01 EST 2020

% Result     : Theorem 28.06s
% Output     : Refutation 28.06s
% Verified   : 
% Statistics : Number of formulae       :  202 ( 492 expanded)
%              Number of leaves         :   31 ( 159 expanded)
%              Depth                    :   37
%              Number of atoms          : 1975 (7438 expanded)
%              Number of equality atoms :  305 (1068 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

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
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_zfmisc_1 @ X14 @ X15 @ X16 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(l139_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i,E: $i] :
            ( ( k4_tarski @ D @ E )
           != A ) ) )).

thf('4',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_tarski @ ( sk_D @ X1 ) @ ( sk_E @ X1 ) )
        = X1 )
      | ~ ( r2_hidden @ X1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k4_tarski @ ( sk_D @ X3 ) @ ( sk_E @ X3 ) )
        = X3 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k4_tarski @ ( sk_D @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
      = sk_E_1 ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('7',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('8',plain,
    ( ( ( k4_tarski @ ( sk_D @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
      = sk_E_1 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k4_tarski @ ( sk_D @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
      = sk_E_1 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('10',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_zfmisc_1 @ X14 @ X15 @ X16 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X5 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k4_tarski @ ( sk_D @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
      = sk_E_1 )
    | ( sk_C = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( ( k4_tarski @ ( sk_D @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
      = sk_E_1 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k4_tarski @ ( sk_D @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
      = sk_E_1 ) ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('17',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X24 @ X25 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('18',plain,
    ( ( ( k1_mcart_1 @ sk_E_1 )
      = ( sk_D @ sk_E_1 ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X5 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('20',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_mcart_1 @ sk_E_1 )
      = ( sk_D @ sk_E_1 ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k1_mcart_1 @ sk_E_1 )
      = ( sk_D @ sk_E_1 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k1_mcart_1 @ sk_E_1 )
    = ( sk_D @ sk_E_1 ) ),
    inference('simplify_reflect-',[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ( ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
      = sk_E_1 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('27',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
      = sk_E_1 )
    | ( sk_C = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
      = sk_E_1 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
      = sk_E_1 ) ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k4_tarski @ ( sk_D @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
      = sk_E_1 ) ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('32',plain,
    ( ( k1_mcart_1 @ sk_E_1 )
    = ( sk_D @ sk_E_1 ) ),
    inference('simplify_reflect-',[status(thm)],['21','22','23'])).

thf('33',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
      = sk_E_1 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X24: $i,X26: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X24 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('35',plain,
    ( ( ( k2_mcart_1 @ sk_E_1 )
      = ( sk_E @ sk_E_1 ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X5 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('37',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_mcart_1 @ sk_E_1 )
      = ( sk_E @ sk_E_1 ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_mcart_1 @ sk_E_1 )
      = ( sk_E @ sk_E_1 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k2_mcart_1 @ sk_E_1 )
    = ( sk_E @ sk_E_1 ) ),
    inference('simplify_reflect-',[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_mcart_1 @ sk_E_1 ) )
      = sk_E_1 ) ),
    inference(demod,[status(thm)],['30','41'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('43',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_mcart_1 @ X11 @ X12 @ X13 )
      = ( k4_tarski @ ( k4_tarski @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k3_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_mcart_1 @ sk_E_1 ) @ X0 )
        = ( k4_tarski @ sk_E_1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X5 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k3_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_mcart_1 @ sk_E_1 ) @ X0 )
        = ( k4_tarski @ sk_E_1 @ X0 ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( ( k3_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_mcart_1 @ sk_E_1 ) @ X0 )
        = ( k4_tarski @ sk_E_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k3_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_mcart_1 @ sk_E_1 ) @ X0 )
      = ( k4_tarski @ sk_E_1 @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['47','48','49'])).

thf('51',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_mcart_1 @ X11 @ X12 @ X13 )
      = ( k4_tarski @ ( k4_tarski @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('52',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X24 @ X25 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ sk_E_1 @ X0 ) )
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_mcart_1 @ sk_E_1 ) ) ) ),
    inference('sup+',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X24 @ X25 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('56',plain,
    ( sk_E_1
    = ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_mcart_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('58',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_zfmisc_1 @ X14 @ X15 @ X16 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('59',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X17 ) @ X18 )
      | ~ ( r2_hidden @ X17 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X17 ) @ X18 )
      | ~ ( r2_hidden @ X17 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('63',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('65',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('67',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A )
    | ( sk_C = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['68','69'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('71',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ X7 @ X8 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('72',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('74',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_tarski @ ( sk_D @ X1 ) @ ( sk_E @ X1 ) )
        = X1 )
      | ~ ( r2_hidden @ X1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('75',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k4_tarski @ ( sk_D @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) )
      = ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k4_tarski @ ( sk_D @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) )
      = ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('77',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X24 @ X25 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('78',plain,
    ( ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
      = ( sk_D @ ( k1_mcart_1 @ sk_E_1 ) ) )
    | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('80',plain,
    ( ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
      = ( sk_D @ ( k1_mcart_1 @ sk_E_1 ) ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('82',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
      = ( sk_D @ ( k1_mcart_1 @ sk_E_1 ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
      = ( sk_D @ ( k1_mcart_1 @ sk_E_1 ) ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
      = ( sk_D @ ( k1_mcart_1 @ sk_E_1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X5 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('87',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
      = ( sk_D @ ( k1_mcart_1 @ sk_E_1 ) ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
      = ( sk_D @ ( k1_mcart_1 @ sk_E_1 ) ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
    = ( sk_D @ ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['88','89','90'])).

thf('92',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) )
      = ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['75','91'])).

thf('93',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) )
      = ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['75','91'])).

thf('94',plain,(
    ! [X24: $i,X26: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X24 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('95',plain,
    ( ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
      = ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) )
    | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('97',plain,
    ( ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
      = ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('99',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
      = ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
      = ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
      = ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X5 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('104',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
      = ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
      = ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
    = ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['105','106','107'])).

thf('109',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
      = ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['92','108'])).

thf('110',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_mcart_1 @ X11 @ X12 @ X13 )
      = ( k4_tarski @ ( k4_tarski @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ X0 )
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ X0 ) )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
       != X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X2 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ X0 )
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ X0 ) )
      | ( sk_C = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['111','115'])).

thf('117',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ X0 )
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('120',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X17 ) @ X19 )
      | ~ ( r2_hidden @ X17 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('121',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('123',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('125',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B )
    | ( sk_C = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ X7 @ X8 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('130',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ sk_B )
      | ( sk_E_1
       != ( k3_mcart_1 @ X28 @ X27 @ X29 ) )
      | ( sk_D_1 = X29 )
      | ~ ( m1_subset_1 @ X29 @ sk_C )
      | ~ ( m1_subset_1 @ X28 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_D_1 = X1 )
      | ( sk_E_1
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( sk_E_1
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( sk_D_1 = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['118','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ( sk_D_1 = X0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( sk_E_1
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( sk_E_1
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( sk_D_1 = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['72','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_C )
      | ( sk_D_1 = X0 )
      | ( sk_E_1
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,
    ( ( sk_E_1 != sk_E_1 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_D_1
      = ( k2_mcart_1 @ sk_E_1 ) )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['56','136'])).

thf('138',plain,
    ( ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C )
    | ( sk_D_1
      = ( k2_mcart_1 @ sk_E_1 ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    sk_D_1
 != ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
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

thf('141',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( X20 = k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X20 @ X21 @ X23 @ X22 )
        = ( k2_mcart_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k3_zfmisc_1 @ X20 @ X21 @ X23 ) )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('142',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 )
      = ( k2_mcart_1 @ sk_E_1 ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 )
    = ( k2_mcart_1 @ sk_E_1 ) ),
    inference('simplify_reflect-',[status(thm)],['142','143','144','145'])).

thf('147',plain,(
    sk_D_1
 != ( k2_mcart_1 @ sk_E_1 ) ),
    inference(demod,[status(thm)],['139','146'])).

thf('148',plain,
    ( ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['138','147'])).

thf('149',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('150',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_zfmisc_1 @ X14 @ X15 @ X16 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('151',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X17 ) @ X19 )
      | ~ ( r2_hidden @ X17 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('152',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['149','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('155',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('157',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C )
    | ( sk_C = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ X7 @ X8 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('162',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['148','162'])).

thf('164',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X5 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('165',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['165'])).

thf('167',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['166','167','168'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0PX1bXh82i
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:06:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 28.06/28.25  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 28.06/28.25  % Solved by: fo/fo7.sh
% 28.06/28.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 28.06/28.25  % done 50504 iterations in 27.790s
% 28.06/28.25  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 28.06/28.25  % SZS output start Refutation
% 28.06/28.25  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 28.06/28.25  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 28.06/28.25  thf(sk_D_1_type, type, sk_D_1: $i).
% 28.06/28.25  thf(sk_D_type, type, sk_D: $i > $i).
% 28.06/28.25  thf(sk_E_1_type, type, sk_E_1: $i).
% 28.06/28.25  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 28.06/28.25  thf(sk_B_type, type, sk_B: $i).
% 28.06/28.25  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 28.06/28.25  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 28.06/28.25  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 28.06/28.25  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 28.06/28.25  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 28.06/28.25  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 28.06/28.25  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 28.06/28.25  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 28.06/28.25  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 28.06/28.25  thf(sk_A_type, type, sk_A: $i).
% 28.06/28.25  thf(sk_C_type, type, sk_C: $i).
% 28.06/28.25  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 28.06/28.25  thf(sk_E_type, type, sk_E: $i > $i).
% 28.06/28.25  thf(t71_mcart_1, conjecture,
% 28.06/28.25    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 28.06/28.25     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 28.06/28.25       ( ( ![F:$i]:
% 28.06/28.25           ( ( m1_subset_1 @ F @ A ) =>
% 28.06/28.25             ( ![G:$i]:
% 28.06/28.25               ( ( m1_subset_1 @ G @ B ) =>
% 28.06/28.25                 ( ![H:$i]:
% 28.06/28.25                   ( ( m1_subset_1 @ H @ C ) =>
% 28.06/28.25                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 28.06/28.25                       ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 28.06/28.25         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 28.06/28.25           ( ( C ) = ( k1_xboole_0 ) ) | 
% 28.06/28.25           ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 28.06/28.25  thf(zf_stmt_0, negated_conjecture,
% 28.06/28.25    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 28.06/28.25        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 28.06/28.25          ( ( ![F:$i]:
% 28.06/28.25              ( ( m1_subset_1 @ F @ A ) =>
% 28.06/28.25                ( ![G:$i]:
% 28.06/28.25                  ( ( m1_subset_1 @ G @ B ) =>
% 28.06/28.25                    ( ![H:$i]:
% 28.06/28.25                      ( ( m1_subset_1 @ H @ C ) =>
% 28.06/28.25                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 28.06/28.25                          ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 28.06/28.25            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 28.06/28.25              ( ( C ) = ( k1_xboole_0 ) ) | 
% 28.06/28.25              ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 28.06/28.25    inference('cnf.neg', [status(esa)], [t71_mcart_1])).
% 28.06/28.25  thf('0', plain,
% 28.06/28.25      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 28.06/28.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.06/28.25  thf(t2_subset, axiom,
% 28.06/28.25    (![A:$i,B:$i]:
% 28.06/28.25     ( ( m1_subset_1 @ A @ B ) =>
% 28.06/28.25       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 28.06/28.25  thf('1', plain,
% 28.06/28.25      (![X9 : $i, X10 : $i]:
% 28.06/28.25         ((r2_hidden @ X9 @ X10)
% 28.06/28.25          | (v1_xboole_0 @ X10)
% 28.06/28.25          | ~ (m1_subset_1 @ X9 @ X10))),
% 28.06/28.25      inference('cnf', [status(esa)], [t2_subset])).
% 28.06/28.25  thf('2', plain,
% 28.06/28.25      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 28.06/28.25        | (r2_hidden @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 28.06/28.25      inference('sup-', [status(thm)], ['0', '1'])).
% 28.06/28.25  thf(d3_zfmisc_1, axiom,
% 28.06/28.25    (![A:$i,B:$i,C:$i]:
% 28.06/28.25     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 28.06/28.25       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 28.06/28.25  thf('3', plain,
% 28.06/28.25      (![X14 : $i, X15 : $i, X16 : $i]:
% 28.06/28.25         ((k3_zfmisc_1 @ X14 @ X15 @ X16)
% 28.06/28.25           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15) @ X16))),
% 28.06/28.25      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 28.06/28.25  thf(l139_zfmisc_1, axiom,
% 28.06/28.25    (![A:$i,B:$i,C:$i]:
% 28.06/28.25     ( ~( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 28.06/28.25          ( ![D:$i,E:$i]: ( ( k4_tarski @ D @ E ) != ( A ) ) ) ) ))).
% 28.06/28.25  thf('4', plain,
% 28.06/28.25      (![X1 : $i, X2 : $i, X3 : $i]:
% 28.06/28.25         (((k4_tarski @ (sk_D @ X1) @ (sk_E @ X1)) = (X1))
% 28.06/28.25          | ~ (r2_hidden @ X1 @ (k2_zfmisc_1 @ X2 @ X3)))),
% 28.06/28.25      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 28.06/28.25  thf('5', plain,
% 28.06/28.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 28.06/28.25         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 28.06/28.25          | ((k4_tarski @ (sk_D @ X3) @ (sk_E @ X3)) = (X3)))),
% 28.06/28.25      inference('sup-', [status(thm)], ['3', '4'])).
% 28.06/28.25  thf('6', plain,
% 28.06/28.25      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 28.06/28.25        | ((k4_tarski @ (sk_D @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1)))),
% 28.06/28.25      inference('sup-', [status(thm)], ['2', '5'])).
% 28.06/28.25  thf(l13_xboole_0, axiom,
% 28.06/28.25    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 28.06/28.25  thf('7', plain,
% 28.06/28.25      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 28.06/28.25      inference('cnf', [status(esa)], [l13_xboole_0])).
% 28.06/28.25  thf('8', plain,
% 28.06/28.25      ((((k4_tarski @ (sk_D @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1))
% 28.06/28.25        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 28.06/28.25      inference('sup-', [status(thm)], ['6', '7'])).
% 28.06/28.25  thf('9', plain,
% 28.06/28.25      ((((k4_tarski @ (sk_D @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1))
% 28.06/28.25        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 28.06/28.25      inference('sup-', [status(thm)], ['6', '7'])).
% 28.06/28.25  thf('10', plain,
% 28.06/28.25      (![X14 : $i, X15 : $i, X16 : $i]:
% 28.06/28.25         ((k3_zfmisc_1 @ X14 @ X15 @ X16)
% 28.06/28.25           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15) @ X16))),
% 28.06/28.25      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 28.06/28.25  thf(t113_zfmisc_1, axiom,
% 28.06/28.25    (![A:$i,B:$i]:
% 28.06/28.25     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 28.06/28.25       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 28.06/28.25  thf('11', plain,
% 28.06/28.25      (![X4 : $i, X5 : $i]:
% 28.06/28.25         (((X4) = (k1_xboole_0))
% 28.06/28.25          | ((X5) = (k1_xboole_0))
% 28.06/28.25          | ((k2_zfmisc_1 @ X5 @ X4) != (k1_xboole_0)))),
% 28.06/28.25      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 28.06/28.25  thf('12', plain,
% 28.06/28.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 28.06/28.25         (((k3_zfmisc_1 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 28.06/28.25          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 28.06/28.25          | ((X0) = (k1_xboole_0)))),
% 28.06/28.25      inference('sup-', [status(thm)], ['10', '11'])).
% 28.06/28.25  thf('13', plain,
% 28.06/28.25      ((((k1_xboole_0) != (k1_xboole_0))
% 28.06/28.25        | ((k4_tarski @ (sk_D @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1))
% 28.06/28.25        | ((sk_C) = (k1_xboole_0))
% 28.06/28.25        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 28.06/28.25      inference('sup-', [status(thm)], ['9', '12'])).
% 28.06/28.25  thf('14', plain,
% 28.06/28.25      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 28.06/28.25        | ((sk_C) = (k1_xboole_0))
% 28.06/28.25        | ((k4_tarski @ (sk_D @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1)))),
% 28.06/28.25      inference('simplify', [status(thm)], ['13'])).
% 28.06/28.25  thf('15', plain, (((sk_C) != (k1_xboole_0))),
% 28.06/28.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.06/28.25  thf('16', plain,
% 28.06/28.25      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 28.06/28.25        | ((k4_tarski @ (sk_D @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1)))),
% 28.06/28.25      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 28.06/28.25  thf(t7_mcart_1, axiom,
% 28.06/28.25    (![A:$i,B:$i]:
% 28.06/28.25     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 28.06/28.25       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 28.06/28.25  thf('17', plain,
% 28.06/28.25      (![X24 : $i, X25 : $i]: ((k1_mcart_1 @ (k4_tarski @ X24 @ X25)) = (X24))),
% 28.06/28.25      inference('cnf', [status(esa)], [t7_mcart_1])).
% 28.06/28.25  thf('18', plain,
% 28.06/28.25      ((((k1_mcart_1 @ sk_E_1) = (sk_D @ sk_E_1))
% 28.06/28.25        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 28.06/28.25      inference('sup+', [status(thm)], ['16', '17'])).
% 28.06/28.25  thf('19', plain,
% 28.06/28.25      (![X4 : $i, X5 : $i]:
% 28.06/28.25         (((X4) = (k1_xboole_0))
% 28.06/28.25          | ((X5) = (k1_xboole_0))
% 28.06/28.25          | ((k2_zfmisc_1 @ X5 @ X4) != (k1_xboole_0)))),
% 28.06/28.25      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 28.06/28.25  thf('20', plain,
% 28.06/28.25      ((((k1_xboole_0) != (k1_xboole_0))
% 28.06/28.25        | ((k1_mcart_1 @ sk_E_1) = (sk_D @ sk_E_1))
% 28.06/28.25        | ((sk_A) = (k1_xboole_0))
% 28.06/28.25        | ((sk_B) = (k1_xboole_0)))),
% 28.06/28.25      inference('sup-', [status(thm)], ['18', '19'])).
% 28.06/28.25  thf('21', plain,
% 28.06/28.25      ((((sk_B) = (k1_xboole_0))
% 28.06/28.25        | ((sk_A) = (k1_xboole_0))
% 28.06/28.25        | ((k1_mcart_1 @ sk_E_1) = (sk_D @ sk_E_1)))),
% 28.06/28.25      inference('simplify', [status(thm)], ['20'])).
% 28.06/28.25  thf('22', plain, (((sk_A) != (k1_xboole_0))),
% 28.06/28.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.06/28.25  thf('23', plain, (((sk_B) != (k1_xboole_0))),
% 28.06/28.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.06/28.25  thf('24', plain, (((k1_mcart_1 @ sk_E_1) = (sk_D @ sk_E_1))),
% 28.06/28.25      inference('simplify_reflect-', [status(thm)], ['21', '22', '23'])).
% 28.06/28.25  thf('25', plain,
% 28.06/28.25      ((((k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1))
% 28.06/28.25        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 28.06/28.25      inference('demod', [status(thm)], ['8', '24'])).
% 28.06/28.25  thf('26', plain,
% 28.06/28.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 28.06/28.25         (((k3_zfmisc_1 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 28.06/28.25          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 28.06/28.25          | ((X0) = (k1_xboole_0)))),
% 28.06/28.25      inference('sup-', [status(thm)], ['10', '11'])).
% 28.06/28.25  thf('27', plain,
% 28.06/28.25      ((((k1_xboole_0) != (k1_xboole_0))
% 28.06/28.25        | ((k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1))
% 28.06/28.25        | ((sk_C) = (k1_xboole_0))
% 28.06/28.25        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 28.06/28.25      inference('sup-', [status(thm)], ['25', '26'])).
% 28.06/28.25  thf('28', plain,
% 28.06/28.25      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 28.06/28.25        | ((sk_C) = (k1_xboole_0))
% 28.06/28.25        | ((k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1)))),
% 28.06/28.25      inference('simplify', [status(thm)], ['27'])).
% 28.06/28.25  thf('29', plain, (((sk_C) != (k1_xboole_0))),
% 28.06/28.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.06/28.25  thf('30', plain,
% 28.06/28.25      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 28.06/28.25        | ((k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1)))),
% 28.06/28.25      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 28.06/28.25  thf('31', plain,
% 28.06/28.25      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 28.06/28.25        | ((k4_tarski @ (sk_D @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1)))),
% 28.06/28.25      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 28.06/28.25  thf('32', plain, (((k1_mcart_1 @ sk_E_1) = (sk_D @ sk_E_1))),
% 28.06/28.25      inference('simplify_reflect-', [status(thm)], ['21', '22', '23'])).
% 28.06/28.25  thf('33', plain,
% 28.06/28.25      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 28.06/28.25        | ((k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1)))),
% 28.06/28.25      inference('demod', [status(thm)], ['31', '32'])).
% 28.06/28.25  thf('34', plain,
% 28.06/28.25      (![X24 : $i, X26 : $i]: ((k2_mcart_1 @ (k4_tarski @ X24 @ X26)) = (X26))),
% 28.06/28.25      inference('cnf', [status(esa)], [t7_mcart_1])).
% 28.06/28.25  thf('35', plain,
% 28.06/28.25      ((((k2_mcart_1 @ sk_E_1) = (sk_E @ sk_E_1))
% 28.06/28.25        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 28.06/28.25      inference('sup+', [status(thm)], ['33', '34'])).
% 28.06/28.25  thf('36', plain,
% 28.06/28.25      (![X4 : $i, X5 : $i]:
% 28.06/28.25         (((X4) = (k1_xboole_0))
% 28.06/28.25          | ((X5) = (k1_xboole_0))
% 28.06/28.25          | ((k2_zfmisc_1 @ X5 @ X4) != (k1_xboole_0)))),
% 28.06/28.25      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 28.06/28.25  thf('37', plain,
% 28.06/28.25      ((((k1_xboole_0) != (k1_xboole_0))
% 28.06/28.25        | ((k2_mcart_1 @ sk_E_1) = (sk_E @ sk_E_1))
% 28.06/28.25        | ((sk_A) = (k1_xboole_0))
% 28.06/28.25        | ((sk_B) = (k1_xboole_0)))),
% 28.06/28.25      inference('sup-', [status(thm)], ['35', '36'])).
% 28.06/28.25  thf('38', plain,
% 28.06/28.25      ((((sk_B) = (k1_xboole_0))
% 28.06/28.25        | ((sk_A) = (k1_xboole_0))
% 28.06/28.25        | ((k2_mcart_1 @ sk_E_1) = (sk_E @ sk_E_1)))),
% 28.06/28.25      inference('simplify', [status(thm)], ['37'])).
% 28.06/28.25  thf('39', plain, (((sk_A) != (k1_xboole_0))),
% 28.06/28.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.06/28.25  thf('40', plain, (((sk_B) != (k1_xboole_0))),
% 28.06/28.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.06/28.25  thf('41', plain, (((k2_mcart_1 @ sk_E_1) = (sk_E @ sk_E_1))),
% 28.06/28.25      inference('simplify_reflect-', [status(thm)], ['38', '39', '40'])).
% 28.06/28.25  thf('42', plain,
% 28.06/28.25      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 28.06/28.25        | ((k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (k2_mcart_1 @ sk_E_1))
% 28.06/28.25            = (sk_E_1)))),
% 28.06/28.25      inference('demod', [status(thm)], ['30', '41'])).
% 28.06/28.25  thf(d3_mcart_1, axiom,
% 28.06/28.25    (![A:$i,B:$i,C:$i]:
% 28.06/28.25     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 28.06/28.25  thf('43', plain,
% 28.06/28.25      (![X11 : $i, X12 : $i, X13 : $i]:
% 28.06/28.25         ((k3_mcart_1 @ X11 @ X12 @ X13)
% 28.06/28.25           = (k4_tarski @ (k4_tarski @ X11 @ X12) @ X13))),
% 28.06/28.25      inference('cnf', [status(esa)], [d3_mcart_1])).
% 28.06/28.25  thf('44', plain,
% 28.06/28.25      (![X0 : $i]:
% 28.06/28.25         (((k3_mcart_1 @ (k1_mcart_1 @ sk_E_1) @ (k2_mcart_1 @ sk_E_1) @ X0)
% 28.06/28.25            = (k4_tarski @ sk_E_1 @ X0))
% 28.06/28.25          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 28.06/28.25      inference('sup+', [status(thm)], ['42', '43'])).
% 28.06/28.25  thf('45', plain,
% 28.06/28.25      (![X4 : $i, X5 : $i]:
% 28.06/28.25         (((X4) = (k1_xboole_0))
% 28.06/28.25          | ((X5) = (k1_xboole_0))
% 28.06/28.25          | ((k2_zfmisc_1 @ X5 @ X4) != (k1_xboole_0)))),
% 28.06/28.25      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 28.06/28.25  thf('46', plain,
% 28.06/28.25      (![X0 : $i]:
% 28.06/28.25         (((k1_xboole_0) != (k1_xboole_0))
% 28.06/28.25          | ((k3_mcart_1 @ (k1_mcart_1 @ sk_E_1) @ (k2_mcart_1 @ sk_E_1) @ X0)
% 28.06/28.25              = (k4_tarski @ sk_E_1 @ X0))
% 28.06/28.25          | ((sk_A) = (k1_xboole_0))
% 28.06/28.25          | ((sk_B) = (k1_xboole_0)))),
% 28.06/28.25      inference('sup-', [status(thm)], ['44', '45'])).
% 28.06/28.25  thf('47', plain,
% 28.06/28.25      (![X0 : $i]:
% 28.06/28.25         (((sk_B) = (k1_xboole_0))
% 28.06/28.25          | ((sk_A) = (k1_xboole_0))
% 28.06/28.25          | ((k3_mcart_1 @ (k1_mcart_1 @ sk_E_1) @ (k2_mcart_1 @ sk_E_1) @ X0)
% 28.06/28.25              = (k4_tarski @ sk_E_1 @ X0)))),
% 28.06/28.25      inference('simplify', [status(thm)], ['46'])).
% 28.06/28.25  thf('48', plain, (((sk_A) != (k1_xboole_0))),
% 28.06/28.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.06/28.25  thf('49', plain, (((sk_B) != (k1_xboole_0))),
% 28.06/28.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.06/28.25  thf('50', plain,
% 28.06/28.25      (![X0 : $i]:
% 28.06/28.25         ((k3_mcart_1 @ (k1_mcart_1 @ sk_E_1) @ (k2_mcart_1 @ sk_E_1) @ X0)
% 28.06/28.25           = (k4_tarski @ sk_E_1 @ X0))),
% 28.06/28.25      inference('simplify_reflect-', [status(thm)], ['47', '48', '49'])).
% 28.06/28.25  thf('51', plain,
% 28.06/28.25      (![X11 : $i, X12 : $i, X13 : $i]:
% 28.06/28.25         ((k3_mcart_1 @ X11 @ X12 @ X13)
% 28.06/28.25           = (k4_tarski @ (k4_tarski @ X11 @ X12) @ X13))),
% 28.06/28.25      inference('cnf', [status(esa)], [d3_mcart_1])).
% 28.06/28.25  thf('52', plain,
% 28.06/28.25      (![X24 : $i, X25 : $i]: ((k1_mcart_1 @ (k4_tarski @ X24 @ X25)) = (X24))),
% 28.06/28.25      inference('cnf', [status(esa)], [t7_mcart_1])).
% 28.06/28.25  thf('53', plain,
% 28.06/28.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 28.06/28.25         ((k1_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (k4_tarski @ X2 @ X1))),
% 28.06/28.25      inference('sup+', [status(thm)], ['51', '52'])).
% 28.06/28.25  thf('54', plain,
% 28.06/28.25      (![X0 : $i]:
% 28.06/28.25         ((k1_mcart_1 @ (k4_tarski @ sk_E_1 @ X0))
% 28.06/28.25           = (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (k2_mcart_1 @ sk_E_1)))),
% 28.06/28.25      inference('sup+', [status(thm)], ['50', '53'])).
% 28.06/28.25  thf('55', plain,
% 28.06/28.25      (![X24 : $i, X25 : $i]: ((k1_mcart_1 @ (k4_tarski @ X24 @ X25)) = (X24))),
% 28.06/28.25      inference('cnf', [status(esa)], [t7_mcart_1])).
% 28.06/28.25  thf('56', plain,
% 28.06/28.25      (((sk_E_1) = (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (k2_mcart_1 @ sk_E_1)))),
% 28.06/28.25      inference('demod', [status(thm)], ['54', '55'])).
% 28.06/28.25  thf('57', plain,
% 28.06/28.25      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 28.06/28.25        | (r2_hidden @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 28.06/28.25      inference('sup-', [status(thm)], ['0', '1'])).
% 28.06/28.25  thf('58', plain,
% 28.06/28.25      (![X14 : $i, X15 : $i, X16 : $i]:
% 28.06/28.25         ((k3_zfmisc_1 @ X14 @ X15 @ X16)
% 28.06/28.25           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15) @ X16))),
% 28.06/28.25      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 28.06/28.25  thf(t10_mcart_1, axiom,
% 28.06/28.25    (![A:$i,B:$i,C:$i]:
% 28.06/28.25     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 28.06/28.25       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 28.06/28.25         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 28.06/28.25  thf('59', plain,
% 28.06/28.25      (![X17 : $i, X18 : $i, X19 : $i]:
% 28.06/28.25         ((r2_hidden @ (k1_mcart_1 @ X17) @ X18)
% 28.06/28.25          | ~ (r2_hidden @ X17 @ (k2_zfmisc_1 @ X18 @ X19)))),
% 28.06/28.25      inference('cnf', [status(esa)], [t10_mcart_1])).
% 28.06/28.25  thf('60', plain,
% 28.06/28.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 28.06/28.25         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 28.06/28.25          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 28.06/28.25      inference('sup-', [status(thm)], ['58', '59'])).
% 28.06/28.25  thf('61', plain,
% 28.06/28.25      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 28.06/28.25        | (r2_hidden @ (k1_mcart_1 @ sk_E_1) @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 28.06/28.25      inference('sup-', [status(thm)], ['57', '60'])).
% 28.06/28.25  thf('62', plain,
% 28.06/28.25      (![X17 : $i, X18 : $i, X19 : $i]:
% 28.06/28.25         ((r2_hidden @ (k1_mcart_1 @ X17) @ X18)
% 28.06/28.25          | ~ (r2_hidden @ X17 @ (k2_zfmisc_1 @ X18 @ X19)))),
% 28.06/28.25      inference('cnf', [status(esa)], [t10_mcart_1])).
% 28.06/28.25  thf('63', plain,
% 28.06/28.25      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 28.06/28.25        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A))),
% 28.06/28.25      inference('sup-', [status(thm)], ['61', '62'])).
% 28.06/28.25  thf('64', plain,
% 28.06/28.25      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 28.06/28.25      inference('cnf', [status(esa)], [l13_xboole_0])).
% 28.06/28.25  thf('65', plain,
% 28.06/28.25      (((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A)
% 28.06/28.25        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 28.06/28.25      inference('sup-', [status(thm)], ['63', '64'])).
% 28.06/28.25  thf('66', plain,
% 28.06/28.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 28.06/28.25         (((k3_zfmisc_1 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 28.06/28.25          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 28.06/28.25          | ((X0) = (k1_xboole_0)))),
% 28.06/28.25      inference('sup-', [status(thm)], ['10', '11'])).
% 28.06/28.25  thf('67', plain,
% 28.06/28.25      ((((k1_xboole_0) != (k1_xboole_0))
% 28.06/28.25        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A)
% 28.06/28.25        | ((sk_C) = (k1_xboole_0))
% 28.06/28.25        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 28.06/28.25      inference('sup-', [status(thm)], ['65', '66'])).
% 28.06/28.25  thf('68', plain,
% 28.06/28.25      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 28.06/28.25        | ((sk_C) = (k1_xboole_0))
% 28.06/28.25        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A))),
% 28.06/28.25      inference('simplify', [status(thm)], ['67'])).
% 28.06/28.25  thf('69', plain, (((sk_C) != (k1_xboole_0))),
% 28.06/28.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.06/28.25  thf('70', plain,
% 28.06/28.25      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 28.06/28.25        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A))),
% 28.06/28.25      inference('simplify_reflect-', [status(thm)], ['68', '69'])).
% 28.06/28.25  thf(t1_subset, axiom,
% 28.06/28.25    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 28.06/28.25  thf('71', plain,
% 28.06/28.25      (![X7 : $i, X8 : $i]: ((m1_subset_1 @ X7 @ X8) | ~ (r2_hidden @ X7 @ X8))),
% 28.06/28.25      inference('cnf', [status(esa)], [t1_subset])).
% 28.06/28.25  thf('72', plain,
% 28.06/28.25      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 28.06/28.25        | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A))),
% 28.06/28.25      inference('sup-', [status(thm)], ['70', '71'])).
% 28.06/28.25  thf('73', plain,
% 28.06/28.25      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 28.06/28.25        | (r2_hidden @ (k1_mcart_1 @ sk_E_1) @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 28.06/28.25      inference('sup-', [status(thm)], ['57', '60'])).
% 28.06/28.25  thf('74', plain,
% 28.06/28.25      (![X1 : $i, X2 : $i, X3 : $i]:
% 28.06/28.25         (((k4_tarski @ (sk_D @ X1) @ (sk_E @ X1)) = (X1))
% 28.06/28.25          | ~ (r2_hidden @ X1 @ (k2_zfmisc_1 @ X2 @ X3)))),
% 28.06/28.25      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 28.06/28.25  thf('75', plain,
% 28.06/28.25      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 28.06/28.25        | ((k4_tarski @ (sk_D @ (k1_mcart_1 @ sk_E_1)) @ 
% 28.06/28.25            (sk_E @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1)))),
% 28.06/28.25      inference('sup-', [status(thm)], ['73', '74'])).
% 28.06/28.25  thf('76', plain,
% 28.06/28.25      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 28.06/28.25        | ((k4_tarski @ (sk_D @ (k1_mcart_1 @ sk_E_1)) @ 
% 28.06/28.25            (sk_E @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1)))),
% 28.06/28.25      inference('sup-', [status(thm)], ['73', '74'])).
% 28.06/28.25  thf('77', plain,
% 28.06/28.25      (![X24 : $i, X25 : $i]: ((k1_mcart_1 @ (k4_tarski @ X24 @ X25)) = (X24))),
% 28.06/28.25      inference('cnf', [status(esa)], [t7_mcart_1])).
% 28.06/28.25  thf('78', plain,
% 28.06/28.25      ((((k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) = (sk_D @ (k1_mcart_1 @ sk_E_1)))
% 28.06/28.25        | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 28.06/28.25      inference('sup+', [status(thm)], ['76', '77'])).
% 28.06/28.25  thf('79', plain,
% 28.06/28.25      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 28.06/28.25      inference('cnf', [status(esa)], [l13_xboole_0])).
% 28.06/28.25  thf('80', plain,
% 28.06/28.25      ((((k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) = (sk_D @ (k1_mcart_1 @ sk_E_1)))
% 28.06/28.25        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 28.06/28.25      inference('sup-', [status(thm)], ['78', '79'])).
% 28.06/28.25  thf('81', plain,
% 28.06/28.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 28.06/28.25         (((k3_zfmisc_1 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 28.06/28.25          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 28.06/28.25          | ((X0) = (k1_xboole_0)))),
% 28.06/28.25      inference('sup-', [status(thm)], ['10', '11'])).
% 28.06/28.25  thf('82', plain,
% 28.06/28.25      ((((k1_xboole_0) != (k1_xboole_0))
% 28.06/28.25        | ((k1_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 28.06/28.25            = (sk_D @ (k1_mcart_1 @ sk_E_1)))
% 28.06/28.25        | ((sk_C) = (k1_xboole_0))
% 28.06/28.25        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 28.06/28.25      inference('sup-', [status(thm)], ['80', '81'])).
% 28.06/28.25  thf('83', plain,
% 28.06/28.25      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 28.06/28.25        | ((sk_C) = (k1_xboole_0))
% 28.06/28.25        | ((k1_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 28.06/28.25            = (sk_D @ (k1_mcart_1 @ sk_E_1))))),
% 28.06/28.25      inference('simplify', [status(thm)], ['82'])).
% 28.06/28.25  thf('84', plain, (((sk_C) != (k1_xboole_0))),
% 28.06/28.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.06/28.25  thf('85', plain,
% 28.06/28.25      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 28.06/28.25        | ((k1_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 28.06/28.25            = (sk_D @ (k1_mcart_1 @ sk_E_1))))),
% 28.06/28.25      inference('simplify_reflect-', [status(thm)], ['83', '84'])).
% 28.06/28.25  thf('86', plain,
% 28.06/28.25      (![X4 : $i, X5 : $i]:
% 28.06/28.25         (((X4) = (k1_xboole_0))
% 28.06/28.25          | ((X5) = (k1_xboole_0))
% 28.06/28.25          | ((k2_zfmisc_1 @ X5 @ X4) != (k1_xboole_0)))),
% 28.06/28.25      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 28.06/28.25  thf('87', plain,
% 28.06/28.25      ((((k1_xboole_0) != (k1_xboole_0))
% 28.06/28.25        | ((k1_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 28.06/28.25            = (sk_D @ (k1_mcart_1 @ sk_E_1)))
% 28.06/28.25        | ((sk_A) = (k1_xboole_0))
% 28.06/28.25        | ((sk_B) = (k1_xboole_0)))),
% 28.06/28.25      inference('sup-', [status(thm)], ['85', '86'])).
% 28.06/28.25  thf('88', plain,
% 28.06/28.25      ((((sk_B) = (k1_xboole_0))
% 28.06/28.25        | ((sk_A) = (k1_xboole_0))
% 28.06/28.25        | ((k1_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 28.06/28.25            = (sk_D @ (k1_mcart_1 @ sk_E_1))))),
% 28.06/28.25      inference('simplify', [status(thm)], ['87'])).
% 28.06/28.25  thf('89', plain, (((sk_A) != (k1_xboole_0))),
% 28.06/28.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.06/28.25  thf('90', plain, (((sk_B) != (k1_xboole_0))),
% 28.06/28.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.06/28.25  thf('91', plain,
% 28.06/28.25      (((k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) = (sk_D @ (k1_mcart_1 @ sk_E_1)))),
% 28.06/28.25      inference('simplify_reflect-', [status(thm)], ['88', '89', '90'])).
% 28.06/28.25  thf('92', plain,
% 28.06/28.25      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 28.06/28.25        | ((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 28.06/28.25            (sk_E @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1)))),
% 28.06/28.25      inference('demod', [status(thm)], ['75', '91'])).
% 28.06/28.25  thf('93', plain,
% 28.06/28.25      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 28.06/28.25        | ((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 28.06/28.25            (sk_E @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1)))),
% 28.06/28.25      inference('demod', [status(thm)], ['75', '91'])).
% 28.06/28.25  thf('94', plain,
% 28.06/28.25      (![X24 : $i, X26 : $i]: ((k2_mcart_1 @ (k4_tarski @ X24 @ X26)) = (X26))),
% 28.06/28.25      inference('cnf', [status(esa)], [t7_mcart_1])).
% 28.06/28.25  thf('95', plain,
% 28.06/28.25      ((((k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) = (sk_E @ (k1_mcart_1 @ sk_E_1)))
% 28.06/28.25        | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 28.06/28.25      inference('sup+', [status(thm)], ['93', '94'])).
% 28.06/28.25  thf('96', plain,
% 28.06/28.25      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 28.06/28.25      inference('cnf', [status(esa)], [l13_xboole_0])).
% 28.06/28.25  thf('97', plain,
% 28.06/28.25      ((((k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) = (sk_E @ (k1_mcart_1 @ sk_E_1)))
% 28.06/28.25        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 28.06/28.25      inference('sup-', [status(thm)], ['95', '96'])).
% 28.06/28.25  thf('98', plain,
% 28.06/28.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 28.06/28.25         (((k3_zfmisc_1 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 28.06/28.25          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 28.06/28.25          | ((X0) = (k1_xboole_0)))),
% 28.06/28.25      inference('sup-', [status(thm)], ['10', '11'])).
% 28.06/28.25  thf('99', plain,
% 28.06/28.25      ((((k1_xboole_0) != (k1_xboole_0))
% 28.06/28.25        | ((k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 28.06/28.25            = (sk_E @ (k1_mcart_1 @ sk_E_1)))
% 28.06/28.25        | ((sk_C) = (k1_xboole_0))
% 28.06/28.25        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 28.06/28.25      inference('sup-', [status(thm)], ['97', '98'])).
% 28.06/28.25  thf('100', plain,
% 28.06/28.25      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 28.06/28.25        | ((sk_C) = (k1_xboole_0))
% 28.06/28.25        | ((k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 28.06/28.25            = (sk_E @ (k1_mcart_1 @ sk_E_1))))),
% 28.06/28.25      inference('simplify', [status(thm)], ['99'])).
% 28.06/28.25  thf('101', plain, (((sk_C) != (k1_xboole_0))),
% 28.06/28.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.06/28.25  thf('102', plain,
% 28.06/28.25      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 28.06/28.25        | ((k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 28.06/28.25            = (sk_E @ (k1_mcart_1 @ sk_E_1))))),
% 28.06/28.25      inference('simplify_reflect-', [status(thm)], ['100', '101'])).
% 28.06/28.25  thf('103', plain,
% 28.06/28.25      (![X4 : $i, X5 : $i]:
% 28.06/28.25         (((X4) = (k1_xboole_0))
% 28.06/28.25          | ((X5) = (k1_xboole_0))
% 28.06/28.25          | ((k2_zfmisc_1 @ X5 @ X4) != (k1_xboole_0)))),
% 28.06/28.25      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 28.06/28.25  thf('104', plain,
% 28.06/28.25      ((((k1_xboole_0) != (k1_xboole_0))
% 28.06/28.25        | ((k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 28.06/28.25            = (sk_E @ (k1_mcart_1 @ sk_E_1)))
% 28.06/28.25        | ((sk_A) = (k1_xboole_0))
% 28.06/28.25        | ((sk_B) = (k1_xboole_0)))),
% 28.06/28.25      inference('sup-', [status(thm)], ['102', '103'])).
% 28.06/28.25  thf('105', plain,
% 28.06/28.25      ((((sk_B) = (k1_xboole_0))
% 28.06/28.25        | ((sk_A) = (k1_xboole_0))
% 28.06/28.25        | ((k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 28.06/28.25            = (sk_E @ (k1_mcart_1 @ sk_E_1))))),
% 28.06/28.25      inference('simplify', [status(thm)], ['104'])).
% 28.06/28.25  thf('106', plain, (((sk_A) != (k1_xboole_0))),
% 28.06/28.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.06/28.25  thf('107', plain, (((sk_B) != (k1_xboole_0))),
% 28.06/28.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.06/28.25  thf('108', plain,
% 28.06/28.25      (((k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) = (sk_E @ (k1_mcart_1 @ sk_E_1)))),
% 28.06/28.25      inference('simplify_reflect-', [status(thm)], ['105', '106', '107'])).
% 28.06/28.25  thf('109', plain,
% 28.06/28.25      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 28.06/28.25        | ((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 28.06/28.25            (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1)))),
% 28.06/28.25      inference('demod', [status(thm)], ['92', '108'])).
% 28.06/28.25  thf('110', plain,
% 28.06/28.25      (![X11 : $i, X12 : $i, X13 : $i]:
% 28.06/28.25         ((k3_mcart_1 @ X11 @ X12 @ X13)
% 28.06/28.25           = (k4_tarski @ (k4_tarski @ X11 @ X12) @ X13))),
% 28.06/28.25      inference('cnf', [status(esa)], [d3_mcart_1])).
% 28.06/28.25  thf('111', plain,
% 28.06/28.25      (![X0 : $i]:
% 28.06/28.25         (((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 28.06/28.25            (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ X0)
% 28.06/28.25            = (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ X0))
% 28.06/28.25          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 28.06/28.25      inference('sup+', [status(thm)], ['109', '110'])).
% 28.06/28.25  thf('112', plain,
% 28.06/28.25      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 28.06/28.25      inference('cnf', [status(esa)], [l13_xboole_0])).
% 28.06/28.25  thf('113', plain,
% 28.06/28.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 28.06/28.25         (((k3_zfmisc_1 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 28.06/28.25          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 28.06/28.25          | ((X0) = (k1_xboole_0)))),
% 28.06/28.25      inference('sup-', [status(thm)], ['10', '11'])).
% 28.06/28.25  thf('114', plain,
% 28.06/28.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 28.06/28.25         (((k3_zfmisc_1 @ X3 @ X2 @ X1) != (X0))
% 28.06/28.25          | ~ (v1_xboole_0 @ X0)
% 28.06/28.25          | ((X1) = (k1_xboole_0))
% 28.06/28.25          | ((k2_zfmisc_1 @ X3 @ X2) = (k1_xboole_0)))),
% 28.06/28.25      inference('sup-', [status(thm)], ['112', '113'])).
% 28.06/28.25  thf('115', plain,
% 28.06/28.25      (![X1 : $i, X2 : $i, X3 : $i]:
% 28.06/28.25         (((k2_zfmisc_1 @ X3 @ X2) = (k1_xboole_0))
% 28.06/28.25          | ((X1) = (k1_xboole_0))
% 28.06/28.25          | ~ (v1_xboole_0 @ (k3_zfmisc_1 @ X3 @ X2 @ X1)))),
% 28.06/28.25      inference('simplify', [status(thm)], ['114'])).
% 28.06/28.25  thf('116', plain,
% 28.06/28.25      (![X0 : $i]:
% 28.06/28.25         (((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 28.06/28.25            (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ X0)
% 28.06/28.25            = (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ X0))
% 28.06/28.25          | ((sk_C) = (k1_xboole_0))
% 28.06/28.25          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 28.06/28.25      inference('sup-', [status(thm)], ['111', '115'])).
% 28.06/28.25  thf('117', plain, (((sk_C) != (k1_xboole_0))),
% 28.06/28.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.06/28.25  thf('118', plain,
% 28.06/28.25      (![X0 : $i]:
% 28.06/28.25         (((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 28.06/28.25            (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ X0)
% 28.06/28.25            = (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ X0))
% 28.06/28.25          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 28.06/28.25      inference('simplify_reflect-', [status(thm)], ['116', '117'])).
% 28.06/28.25  thf('119', plain,
% 28.06/28.25      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 28.06/28.25        | (r2_hidden @ (k1_mcart_1 @ sk_E_1) @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 28.06/28.25      inference('sup-', [status(thm)], ['57', '60'])).
% 28.06/28.25  thf('120', plain,
% 28.06/28.25      (![X17 : $i, X18 : $i, X19 : $i]:
% 28.06/28.25         ((r2_hidden @ (k2_mcart_1 @ X17) @ X19)
% 28.06/28.25          | ~ (r2_hidden @ X17 @ (k2_zfmisc_1 @ X18 @ X19)))),
% 28.06/28.25      inference('cnf', [status(esa)], [t10_mcart_1])).
% 28.06/28.25  thf('121', plain,
% 28.06/28.25      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 28.06/28.25        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B))),
% 28.06/28.25      inference('sup-', [status(thm)], ['119', '120'])).
% 28.06/28.25  thf('122', plain,
% 28.06/28.25      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 28.06/28.25      inference('cnf', [status(esa)], [l13_xboole_0])).
% 28.06/28.25  thf('123', plain,
% 28.06/28.25      (((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B)
% 28.06/28.25        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 28.06/28.25      inference('sup-', [status(thm)], ['121', '122'])).
% 28.06/28.25  thf('124', plain,
% 28.06/28.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 28.06/28.25         (((k3_zfmisc_1 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 28.06/28.25          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 28.06/28.25          | ((X0) = (k1_xboole_0)))),
% 28.06/28.25      inference('sup-', [status(thm)], ['10', '11'])).
% 28.06/28.25  thf('125', plain,
% 28.06/28.25      ((((k1_xboole_0) != (k1_xboole_0))
% 28.06/28.25        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B)
% 28.06/28.25        | ((sk_C) = (k1_xboole_0))
% 28.06/28.25        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 28.06/28.25      inference('sup-', [status(thm)], ['123', '124'])).
% 28.06/28.25  thf('126', plain,
% 28.06/28.25      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 28.06/28.25        | ((sk_C) = (k1_xboole_0))
% 28.06/28.25        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B))),
% 28.06/28.25      inference('simplify', [status(thm)], ['125'])).
% 28.06/28.25  thf('127', plain, (((sk_C) != (k1_xboole_0))),
% 28.06/28.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.06/28.25  thf('128', plain,
% 28.06/28.25      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 28.06/28.25        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B))),
% 28.06/28.25      inference('simplify_reflect-', [status(thm)], ['126', '127'])).
% 28.06/28.25  thf('129', plain,
% 28.06/28.25      (![X7 : $i, X8 : $i]: ((m1_subset_1 @ X7 @ X8) | ~ (r2_hidden @ X7 @ X8))),
% 28.06/28.25      inference('cnf', [status(esa)], [t1_subset])).
% 28.06/28.25  thf('130', plain,
% 28.06/28.25      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 28.06/28.25        | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B))),
% 28.06/28.25      inference('sup-', [status(thm)], ['128', '129'])).
% 28.06/28.25  thf('131', plain,
% 28.06/28.25      (![X27 : $i, X28 : $i, X29 : $i]:
% 28.06/28.25         (~ (m1_subset_1 @ X27 @ sk_B)
% 28.06/28.25          | ((sk_E_1) != (k3_mcart_1 @ X28 @ X27 @ X29))
% 28.06/28.25          | ((sk_D_1) = (X29))
% 28.06/28.25          | ~ (m1_subset_1 @ X29 @ sk_C)
% 28.06/28.25          | ~ (m1_subset_1 @ X28 @ sk_A))),
% 28.06/28.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.06/28.25  thf('132', plain,
% 28.06/28.25      (![X0 : $i, X1 : $i]:
% 28.06/28.25         (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 28.06/28.25          | ~ (m1_subset_1 @ X0 @ sk_A)
% 28.06/28.25          | ~ (m1_subset_1 @ X1 @ sk_C)
% 28.06/28.25          | ((sk_D_1) = (X1))
% 28.06/28.25          | ((sk_E_1)
% 28.06/28.25              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ X1)))),
% 28.06/28.25      inference('sup-', [status(thm)], ['130', '131'])).
% 28.06/28.25  thf('133', plain,
% 28.06/28.25      (![X0 : $i]:
% 28.06/28.25         (((sk_E_1) != (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ X0))
% 28.06/28.25          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 28.06/28.25          | ((sk_D_1) = (X0))
% 28.06/28.25          | ~ (m1_subset_1 @ X0 @ sk_C)
% 28.06/28.25          | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A)
% 28.06/28.25          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 28.06/28.25      inference('sup-', [status(thm)], ['118', '132'])).
% 28.06/28.25  thf('134', plain,
% 28.06/28.25      (![X0 : $i]:
% 28.06/28.25         (~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A)
% 28.06/28.25          | ~ (m1_subset_1 @ X0 @ sk_C)
% 28.06/28.25          | ((sk_D_1) = (X0))
% 28.06/28.25          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 28.06/28.25          | ((sk_E_1) != (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ X0)))),
% 28.06/28.25      inference('simplify', [status(thm)], ['133'])).
% 28.06/28.25  thf('135', plain,
% 28.06/28.25      (![X0 : $i]:
% 28.06/28.25         (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 28.06/28.25          | ((sk_E_1) != (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ X0))
% 28.06/28.25          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 28.06/28.25          | ((sk_D_1) = (X0))
% 28.06/28.25          | ~ (m1_subset_1 @ X0 @ sk_C))),
% 28.06/28.25      inference('sup-', [status(thm)], ['72', '134'])).
% 28.06/28.25  thf('136', plain,
% 28.06/28.25      (![X0 : $i]:
% 28.06/28.25         (~ (m1_subset_1 @ X0 @ sk_C)
% 28.06/28.25          | ((sk_D_1) = (X0))
% 28.06/28.25          | ((sk_E_1) != (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ X0))
% 28.06/28.25          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 28.06/28.25      inference('simplify', [status(thm)], ['135'])).
% 28.06/28.25  thf('137', plain,
% 28.06/28.25      ((((sk_E_1) != (sk_E_1))
% 28.06/28.25        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 28.06/28.25        | ((sk_D_1) = (k2_mcart_1 @ sk_E_1))
% 28.06/28.25        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E_1) @ sk_C))),
% 28.06/28.25      inference('sup-', [status(thm)], ['56', '136'])).
% 28.06/28.25  thf('138', plain,
% 28.06/28.25      ((~ (m1_subset_1 @ (k2_mcart_1 @ sk_E_1) @ sk_C)
% 28.06/28.25        | ((sk_D_1) = (k2_mcart_1 @ sk_E_1))
% 28.06/28.25        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 28.06/28.25      inference('simplify', [status(thm)], ['137'])).
% 28.06/28.25  thf('139', plain, (((sk_D_1) != (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1))),
% 28.06/28.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.06/28.25  thf('140', plain,
% 28.06/28.25      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 28.06/28.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.06/28.25  thf(t50_mcart_1, axiom,
% 28.06/28.25    (![A:$i,B:$i,C:$i]:
% 28.06/28.25     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 28.06/28.25          ( ( C ) != ( k1_xboole_0 ) ) & 
% 28.06/28.25          ( ~( ![D:$i]:
% 28.06/28.25               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 28.06/28.25                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 28.06/28.25                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 28.06/28.25                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 28.06/28.25                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 28.06/28.25                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 28.06/28.25  thf('141', plain,
% 28.06/28.25      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 28.06/28.25         (((X20) = (k1_xboole_0))
% 28.06/28.25          | ((X21) = (k1_xboole_0))
% 28.06/28.25          | ((k7_mcart_1 @ X20 @ X21 @ X23 @ X22) = (k2_mcart_1 @ X22))
% 28.06/28.25          | ~ (m1_subset_1 @ X22 @ (k3_zfmisc_1 @ X20 @ X21 @ X23))
% 28.06/28.25          | ((X23) = (k1_xboole_0)))),
% 28.06/28.25      inference('cnf', [status(esa)], [t50_mcart_1])).
% 28.06/28.25  thf('142', plain,
% 28.06/28.25      ((((sk_C) = (k1_xboole_0))
% 28.06/28.25        | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1) = (k2_mcart_1 @ sk_E_1))
% 28.06/28.25        | ((sk_B) = (k1_xboole_0))
% 28.06/28.25        | ((sk_A) = (k1_xboole_0)))),
% 28.06/28.25      inference('sup-', [status(thm)], ['140', '141'])).
% 28.06/28.25  thf('143', plain, (((sk_A) != (k1_xboole_0))),
% 28.06/28.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.06/28.25  thf('144', plain, (((sk_B) != (k1_xboole_0))),
% 28.06/28.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.06/28.25  thf('145', plain, (((sk_C) != (k1_xboole_0))),
% 28.06/28.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.06/28.25  thf('146', plain,
% 28.06/28.25      (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1) = (k2_mcart_1 @ sk_E_1))),
% 28.06/28.25      inference('simplify_reflect-', [status(thm)],
% 28.06/28.25                ['142', '143', '144', '145'])).
% 28.06/28.25  thf('147', plain, (((sk_D_1) != (k2_mcart_1 @ sk_E_1))),
% 28.06/28.25      inference('demod', [status(thm)], ['139', '146'])).
% 28.06/28.25  thf('148', plain,
% 28.06/28.25      ((~ (m1_subset_1 @ (k2_mcart_1 @ sk_E_1) @ sk_C)
% 28.06/28.25        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 28.06/28.25      inference('simplify_reflect-', [status(thm)], ['138', '147'])).
% 28.06/28.25  thf('149', plain,
% 28.06/28.25      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 28.06/28.25        | (r2_hidden @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 28.06/28.25      inference('sup-', [status(thm)], ['0', '1'])).
% 28.06/28.25  thf('150', plain,
% 28.06/28.25      (![X14 : $i, X15 : $i, X16 : $i]:
% 28.06/28.25         ((k3_zfmisc_1 @ X14 @ X15 @ X16)
% 28.06/28.25           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15) @ X16))),
% 28.06/28.25      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 28.06/28.25  thf('151', plain,
% 28.06/28.25      (![X17 : $i, X18 : $i, X19 : $i]:
% 28.06/28.25         ((r2_hidden @ (k2_mcart_1 @ X17) @ X19)
% 28.06/28.25          | ~ (r2_hidden @ X17 @ (k2_zfmisc_1 @ X18 @ X19)))),
% 28.06/28.25      inference('cnf', [status(esa)], [t10_mcart_1])).
% 28.06/28.25  thf('152', plain,
% 28.06/28.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 28.06/28.25         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 28.06/28.25          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 28.06/28.25      inference('sup-', [status(thm)], ['150', '151'])).
% 28.06/28.25  thf('153', plain,
% 28.06/28.25      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 28.06/28.25        | (r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C))),
% 28.06/28.25      inference('sup-', [status(thm)], ['149', '152'])).
% 28.06/28.25  thf('154', plain,
% 28.06/28.25      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 28.06/28.25      inference('cnf', [status(esa)], [l13_xboole_0])).
% 28.06/28.25  thf('155', plain,
% 28.06/28.25      (((r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C)
% 28.06/28.25        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 28.06/28.25      inference('sup-', [status(thm)], ['153', '154'])).
% 28.06/28.25  thf('156', plain,
% 28.06/28.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 28.06/28.25         (((k3_zfmisc_1 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 28.06/28.25          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 28.06/28.25          | ((X0) = (k1_xboole_0)))),
% 28.06/28.25      inference('sup-', [status(thm)], ['10', '11'])).
% 28.06/28.25  thf('157', plain,
% 28.06/28.25      ((((k1_xboole_0) != (k1_xboole_0))
% 28.06/28.25        | (r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C)
% 28.06/28.25        | ((sk_C) = (k1_xboole_0))
% 28.06/28.25        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 28.06/28.25      inference('sup-', [status(thm)], ['155', '156'])).
% 28.06/28.25  thf('158', plain,
% 28.06/28.25      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 28.06/28.25        | ((sk_C) = (k1_xboole_0))
% 28.06/28.25        | (r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C))),
% 28.06/28.25      inference('simplify', [status(thm)], ['157'])).
% 28.06/28.25  thf('159', plain, (((sk_C) != (k1_xboole_0))),
% 28.06/28.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.06/28.25  thf('160', plain,
% 28.06/28.25      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 28.06/28.25        | (r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C))),
% 28.06/28.25      inference('simplify_reflect-', [status(thm)], ['158', '159'])).
% 28.06/28.25  thf('161', plain,
% 28.06/28.25      (![X7 : $i, X8 : $i]: ((m1_subset_1 @ X7 @ X8) | ~ (r2_hidden @ X7 @ X8))),
% 28.06/28.25      inference('cnf', [status(esa)], [t1_subset])).
% 28.06/28.25  thf('162', plain,
% 28.06/28.25      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 28.06/28.25        | (m1_subset_1 @ (k2_mcart_1 @ sk_E_1) @ sk_C))),
% 28.06/28.25      inference('sup-', [status(thm)], ['160', '161'])).
% 28.06/28.25  thf('163', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 28.06/28.25      inference('clc', [status(thm)], ['148', '162'])).
% 28.06/28.25  thf('164', plain,
% 28.06/28.25      (![X4 : $i, X5 : $i]:
% 28.06/28.25         (((X4) = (k1_xboole_0))
% 28.06/28.25          | ((X5) = (k1_xboole_0))
% 28.06/28.25          | ((k2_zfmisc_1 @ X5 @ X4) != (k1_xboole_0)))),
% 28.06/28.25      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 28.06/28.25  thf('165', plain,
% 28.06/28.25      ((((k1_xboole_0) != (k1_xboole_0))
% 28.06/28.25        | ((sk_A) = (k1_xboole_0))
% 28.06/28.25        | ((sk_B) = (k1_xboole_0)))),
% 28.06/28.25      inference('sup-', [status(thm)], ['163', '164'])).
% 28.06/28.25  thf('166', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 28.06/28.25      inference('simplify', [status(thm)], ['165'])).
% 28.06/28.25  thf('167', plain, (((sk_A) != (k1_xboole_0))),
% 28.06/28.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.06/28.25  thf('168', plain, (((sk_B) != (k1_xboole_0))),
% 28.06/28.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.06/28.25  thf('169', plain, ($false),
% 28.06/28.25      inference('simplify_reflect-', [status(thm)], ['166', '167', '168'])).
% 28.06/28.25  
% 28.06/28.25  % SZS output end Refutation
% 28.06/28.25  
% 28.06/28.25  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
