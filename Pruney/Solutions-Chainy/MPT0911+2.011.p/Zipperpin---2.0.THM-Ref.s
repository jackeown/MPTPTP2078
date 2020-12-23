%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gLtqkxxkGl

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:57 EST 2020

% Result     : Theorem 2.11s
% Output     : Refutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :  251 (1210 expanded)
%              Number of leaves         :   41 ( 378 expanded)
%              Depth                    :   41
%              Number of atoms          : 2303 (17795 expanded)
%              Number of equality atoms :  346 (2471 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r2_hidden @ X21 @ X22 )
      | ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('3',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k3_zfmisc_1 @ X26 @ X27 @ X28 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(l139_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i,E: $i] :
            ( ( k4_tarski @ D @ E )
           != A ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k4_tarski @ ( sk_D_1 @ X11 ) @ ( sk_E @ X11 ) )
        = X11 )
      | ~ ( r2_hidden @ X11 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k4_tarski @ ( sk_D_1 @ X3 ) @ ( sk_E @ X3 ) )
        = X3 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( ( k4_tarski @ ( sk_D_1 @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
      = sk_E_1 ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t34_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) )).

thf('7',plain,(
    ! [X36: $i] :
      ( ( X36 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X36 ) @ X36 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( k4_tarski @ ( sk_D_1 @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
      = sk_E_1 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k3_zfmisc_1 @ X26 @ X27 @ X28 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('12',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X15 @ X14 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k4_tarski @ ( sk_D_1 @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
      = sk_E_1 )
    | ( sk_C = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( ( k4_tarski @ ( sk_D_1 @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
      = sk_E_1 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
    | ( ( k4_tarski @ ( sk_D_1 @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
      = sk_E_1 ) ),
    inference('simplify_reflect-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( ( k4_tarski @ ( sk_D_1 @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
      = sk_E_1 ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('19',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k3_zfmisc_1 @ X26 @ X27 @ X28 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('21',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X15 @ X14 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X1 )
       != X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X1: $i,X2: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf('25',plain,
    ( ( ( k4_tarski @ ( sk_D_1 @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
      = sk_E_1 )
    | ( sk_C = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','24'])).

thf('26',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( ( k4_tarski @ ( sk_D_1 @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
      = sk_E_1 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('28',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X50 @ X51 ) )
      = X50 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('29',plain,
    ( ( ( k1_mcart_1 @ sk_E_1 )
      = ( sk_D_1 @ sk_E_1 ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X15 @ X14 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('31',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_mcart_1 @ sk_E_1 )
      = ( sk_D_1 @ sk_E_1 ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k1_mcart_1 @ sk_E_1 )
      = ( sk_D_1 @ sk_E_1 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k1_mcart_1 @ sk_E_1 )
    = ( sk_D_1 @ sk_E_1 ) ),
    inference('simplify_reflect-',[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
    | ( ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
      = sk_E_1 ) ),
    inference(demod,[status(thm)],['17','35'])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('38',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k3_zfmisc_1 @ X26 @ X27 @ X28 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('39',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X33 ) @ X34 )
      | ~ ( r2_hidden @ X33 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k4_tarski @ ( sk_D_1 @ X11 ) @ ( sk_E @ X11 ) )
        = X11 )
      | ~ ( r2_hidden @ X11 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( ( k4_tarski @ ( sk_D_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) )
      = ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( ( k4_tarski @ ( sk_D_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) )
      = ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('45',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X50 @ X51 ) )
      = X50 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('46',plain,
    ( ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
      = ( sk_D_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
    | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf('48',plain,
    ( ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
      = ( sk_D_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
      = ( sk_D_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X15 @ X14 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('52',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
      = ( sk_D_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
      = ( sk_D_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
    = ( sk_D_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['53','54','55'])).

thf('57',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) )
      = ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['43','56'])).

thf('58',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) )
      = ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['43','56'])).

thf('59',plain,(
    ! [X50: $i,X52: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X50 @ X52 ) )
      = X52 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('60',plain,
    ( ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
      = ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) )
    | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf('62',plain,
    ( ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
      = ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
      = ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X15 @ X14 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('66',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
      = ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
      = ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
    = ( sk_E @ ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
      = ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['57','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('73',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_zfmisc_1 @ X15 @ X16 )
        = k1_xboole_0 )
      | ( X15 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('74',plain,(
    ! [X16: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X16 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['72','74'])).

thf('76',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
      = ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['57','70'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
        = ( k1_mcart_1 @ sk_E_1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('81',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k4_zfmisc_1 @ X29 @ X30 @ X31 @ X32 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X29 @ X30 @ X31 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X1 )
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
        = ( k1_mcart_1 @ sk_E_1 ) ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
        = ( k1_mcart_1 @ sk_E_1 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['75','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
        = ( k1_mcart_1 @ sk_E_1 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
        = ( k1_mcart_1 @ sk_E_1 ) )
      | ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
        = ( k1_mcart_1 @ sk_E_1 ) ) ) ),
    inference('sup-',[status(thm)],['71','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
        = ( k1_mcart_1 @ sk_E_1 ) ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf(t55_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 ) )
    <=> ( ( k4_zfmisc_1 @ A @ B @ C @ D )
       != k1_xboole_0 ) ) )).

thf('87',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( ( k4_zfmisc_1 @ X45 @ X46 @ X47 @ X48 )
       != k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ( X46 = k1_xboole_0 )
      | ( X45 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
        = ( k1_mcart_1 @ sk_E_1 ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
        = ( k1_mcart_1 @ sk_E_1 ) ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
        = ( k1_mcart_1 @ sk_E_1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['89','90','91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
        = ( k1_mcart_1 @ sk_E_1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['89','90','91','92'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
        = ( k1_mcart_1 @ sk_E_1 ) )
      | ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
        = ( k1_mcart_1 @ sk_E_1 ) ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
        = ( k1_mcart_1 @ sk_E_1 ) )
      | ( X1 = X0 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
    = ( k1_mcart_1 @ sk_E_1 ) ),
    inference(condensation,[status(thm)],['96'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('98',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k3_mcart_1 @ X23 @ X24 @ X25 )
      = ( k4_tarski @ ( k4_tarski @ X23 @ X24 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ X0 )
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('101',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X33 ) @ X35 )
      | ~ ( r2_hidden @ X33 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('102',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('104',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_2 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k4_zfmisc_1 @ X29 @ X30 @ X31 @ X32 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X29 @ X30 @ X31 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X16: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X16 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( ( k4_zfmisc_1 @ X45 @ X46 @ X47 @ X48 )
       != k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ( X46 = k1_xboole_0 )
      | ( X45 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_2 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['111','112','113','114'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('116',plain,(
    ! [X19: $i,X20: $i] :
      ( ( m1_subset_1 @ X19 @ X20 )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('119',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_zfmisc_1 @ X15 @ X16 )
        = k1_xboole_0 )
      | ( X16 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('120',plain,(
    ! [X15: $i] :
      ( ( k2_zfmisc_1 @ X15 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['119'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('121',plain,(
    ! [X17: $i,X18: $i] :
      ~ ( r2_hidden @ X17 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('122',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['118','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['117','123'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('125',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X4 != X3 )
      | ( r2_hidden @ X4 @ X5 )
      | ( X5
       != ( k2_tarski @ X6 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('126',plain,(
    ! [X3: $i,X6: $i] :
      ( r2_hidden @ X3 @ ( k2_tarski @ X6 @ X3 ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_B_2 ),
    inference('sup-',[status(thm)],['124','128'])).

thf('130',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ~ ( m1_subset_1 @ X53 @ sk_B_2 )
      | ( sk_E_1
       != ( k3_mcart_1 @ X54 @ X53 @ X55 ) )
      | ( sk_D_2 = X55 )
      | ~ ( m1_subset_1 @ X55 @ sk_C )
      | ~ ( m1_subset_1 @ X54 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_D_2 = X1 )
      | ( sk_E_1
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( sk_E_1
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ X0 ) )
      | ( sk_D_2 = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['99','131'])).

thf('133',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('134',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X33 ) @ X34 )
      | ~ ( r2_hidden @ X33 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('135',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('137',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k4_zfmisc_1 @ X29 @ X30 @ X31 @ X32 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X29 @ X30 @ X31 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X16: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X16 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( ( k4_zfmisc_1 @ X45 @ X46 @ X47 @ X48 )
       != k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ( X46 = k1_xboole_0 )
      | ( X45 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['144','145','146','147'])).

thf('149',plain,(
    ! [X19: $i,X20: $i] :
      ( ( m1_subset_1 @ X19 @ X20 )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['118','122'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('154',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) @ sk_A ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( sk_E_1
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ X0 ) )
      | ( sk_D_2 = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['132','154'])).

thf('156',plain,
    ( ( sk_E_1 != sk_E_1 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_E_1 ) @ sk_C )
    | ( sk_D_2
      = ( sk_E @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['36','155'])).

thf('157',plain,
    ( ( sk_D_2
      = ( sk_E @ sk_E_1 ) )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_E_1 ) @ sk_C )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
    | ( ( k4_tarski @ ( k1_mcart_1 @ sk_E_1 ) @ ( sk_E @ sk_E_1 ) )
      = sk_E_1 ) ),
    inference(demod,[status(thm)],['17','35'])).

thf('159',plain,(
    ! [X50: $i,X52: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X50 @ X52 ) )
      = X52 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('160',plain,
    ( ( ( k2_mcart_1 @ sk_E_1 )
      = ( sk_E @ sk_E_1 ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X15 @ X14 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('162',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_mcart_1 @ sk_E_1 )
      = ( sk_E @ sk_E_1 ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_mcart_1 @ sk_E_1 )
      = ( sk_E @ sk_E_1 ) ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( k2_mcart_1 @ sk_E_1 )
    = ( sk_E @ sk_E_1 ) ),
    inference('simplify_reflect-',[status(thm)],['163','164','165'])).

thf('167',plain,
    ( ( k2_mcart_1 @ sk_E_1 )
    = ( sk_E @ sk_E_1 ) ),
    inference('simplify_reflect-',[status(thm)],['163','164','165'])).

thf('168',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('169',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k3_zfmisc_1 @ X26 @ X27 @ X28 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('170',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X33 ) @ X35 )
      | ~ ( r2_hidden @ X33 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('171',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) )
    | ( r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['168','171'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('174',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k4_zfmisc_1 @ X29 @ X30 @ X31 @ X32 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X29 @ X30 @ X31 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X16: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X16 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( ( k4_zfmisc_1 @ X45 @ X46 @ X47 @ X48 )
       != k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ( X46 = k1_xboole_0 )
      | ( X45 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C ) ) ),
    inference(simplify,[status(thm)],['180'])).

thf('182',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['181','182','183','184'])).

thf('186',plain,(
    ! [X19: $i,X20: $i] :
      ( ( m1_subset_1 @ X19 @ X20 )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['118','122'])).

thf('189',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['187','188'])).

thf('190',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('191',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_E_1 ) @ sk_C ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,
    ( ( sk_D_2
      = ( k2_mcart_1 @ sk_E_1 ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['157','166','167','191'])).

thf('193',plain,(
    sk_D_2
 != ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
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

thf('195',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( X41 = k1_xboole_0 )
      | ( X42 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X41 @ X42 @ X44 @ X43 )
        = ( k2_mcart_1 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k3_zfmisc_1 @ X41 @ X42 @ X44 ) )
      | ( X44 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('196',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_1 )
      = ( k2_mcart_1 @ sk_E_1 ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_1 )
    = ( k2_mcart_1 @ sk_E_1 ) ),
    inference('simplify_reflect-',[status(thm)],['196','197','198','199'])).

thf('201',plain,(
    sk_D_2
 != ( k2_mcart_1 @ sk_E_1 ) ),
    inference(demod,[status(thm)],['193','200'])).

thf('202',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['192','201'])).

thf('203',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X15 @ X14 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('204',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['204'])).

thf('206',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['205','206','207'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gLtqkxxkGl
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:49:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 2.11/2.35  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.11/2.35  % Solved by: fo/fo7.sh
% 2.11/2.35  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.11/2.35  % done 2604 iterations in 1.895s
% 2.11/2.35  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.11/2.35  % SZS output start Refutation
% 2.11/2.35  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 2.11/2.35  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 2.11/2.35  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 2.11/2.35  thf(sk_B_type, type, sk_B: $i > $i).
% 2.11/2.35  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.11/2.35  thf(sk_B_2_type, type, sk_B_2: $i).
% 2.11/2.35  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 2.11/2.35  thf(sk_E_type, type, sk_E: $i > $i).
% 2.11/2.35  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.11/2.35  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 2.11/2.35  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.11/2.35  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 2.11/2.35  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.11/2.35  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.11/2.35  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 2.11/2.35  thf(sk_D_2_type, type, sk_D_2: $i).
% 2.11/2.35  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 2.11/2.35  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 2.11/2.35  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 2.11/2.35  thf(sk_E_1_type, type, sk_E_1: $i).
% 2.11/2.35  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 2.11/2.35  thf(sk_D_1_type, type, sk_D_1: $i > $i).
% 2.11/2.35  thf(sk_C_type, type, sk_C: $i).
% 2.11/2.35  thf(sk_A_type, type, sk_A: $i).
% 2.11/2.35  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.11/2.35  thf(t71_mcart_1, conjecture,
% 2.11/2.35    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 2.11/2.35     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 2.11/2.35       ( ( ![F:$i]:
% 2.11/2.35           ( ( m1_subset_1 @ F @ A ) =>
% 2.11/2.35             ( ![G:$i]:
% 2.11/2.35               ( ( m1_subset_1 @ G @ B ) =>
% 2.11/2.35                 ( ![H:$i]:
% 2.11/2.35                   ( ( m1_subset_1 @ H @ C ) =>
% 2.11/2.35                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 2.11/2.35                       ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 2.11/2.35         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.11/2.35           ( ( C ) = ( k1_xboole_0 ) ) | 
% 2.11/2.35           ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 2.11/2.35  thf(zf_stmt_0, negated_conjecture,
% 2.11/2.35    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 2.11/2.35        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 2.11/2.35          ( ( ![F:$i]:
% 2.11/2.35              ( ( m1_subset_1 @ F @ A ) =>
% 2.11/2.35                ( ![G:$i]:
% 2.11/2.35                  ( ( m1_subset_1 @ G @ B ) =>
% 2.11/2.35                    ( ![H:$i]:
% 2.11/2.35                      ( ( m1_subset_1 @ H @ C ) =>
% 2.11/2.35                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 2.11/2.35                          ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 2.11/2.35            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.11/2.35              ( ( C ) = ( k1_xboole_0 ) ) | 
% 2.11/2.35              ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 2.11/2.35    inference('cnf.neg', [status(esa)], [t71_mcart_1])).
% 2.11/2.35  thf('0', plain,
% 2.11/2.35      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 2.11/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.35  thf(t2_subset, axiom,
% 2.11/2.35    (![A:$i,B:$i]:
% 2.11/2.35     ( ( m1_subset_1 @ A @ B ) =>
% 2.11/2.35       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 2.11/2.35  thf('1', plain,
% 2.11/2.35      (![X21 : $i, X22 : $i]:
% 2.11/2.35         ((r2_hidden @ X21 @ X22)
% 2.11/2.35          | (v1_xboole_0 @ X22)
% 2.11/2.35          | ~ (m1_subset_1 @ X21 @ X22))),
% 2.11/2.35      inference('cnf', [status(esa)], [t2_subset])).
% 2.11/2.35  thf('2', plain,
% 2.11/2.35      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 2.11/2.35        | (r2_hidden @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 2.11/2.35      inference('sup-', [status(thm)], ['0', '1'])).
% 2.11/2.35  thf(d3_zfmisc_1, axiom,
% 2.11/2.35    (![A:$i,B:$i,C:$i]:
% 2.11/2.35     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 2.11/2.35       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 2.11/2.35  thf('3', plain,
% 2.11/2.35      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.11/2.35         ((k3_zfmisc_1 @ X26 @ X27 @ X28)
% 2.11/2.35           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27) @ X28))),
% 2.11/2.35      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 2.11/2.35  thf(l139_zfmisc_1, axiom,
% 2.11/2.35    (![A:$i,B:$i,C:$i]:
% 2.11/2.35     ( ~( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 2.11/2.35          ( ![D:$i,E:$i]: ( ( k4_tarski @ D @ E ) != ( A ) ) ) ) ))).
% 2.11/2.35  thf('4', plain,
% 2.11/2.35      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.11/2.35         (((k4_tarski @ (sk_D_1 @ X11) @ (sk_E @ X11)) = (X11))
% 2.11/2.35          | ~ (r2_hidden @ X11 @ (k2_zfmisc_1 @ X12 @ X13)))),
% 2.11/2.35      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 2.11/2.35  thf('5', plain,
% 2.11/2.35      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.11/2.35         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 2.11/2.35          | ((k4_tarski @ (sk_D_1 @ X3) @ (sk_E @ X3)) = (X3)))),
% 2.11/2.35      inference('sup-', [status(thm)], ['3', '4'])).
% 2.11/2.35  thf('6', plain,
% 2.11/2.35      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 2.11/2.35        | ((k4_tarski @ (sk_D_1 @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1)))),
% 2.11/2.35      inference('sup-', [status(thm)], ['2', '5'])).
% 2.11/2.35  thf(t34_mcart_1, axiom,
% 2.11/2.35    (![A:$i]:
% 2.11/2.35     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 2.11/2.35          ( ![B:$i]:
% 2.11/2.35            ( ~( ( r2_hidden @ B @ A ) & 
% 2.11/2.35                 ( ![C:$i,D:$i,E:$i,F:$i]:
% 2.11/2.35                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 2.11/2.35                        ( ( B ) = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) ) ) ) ) ))).
% 2.11/2.35  thf('7', plain,
% 2.11/2.35      (![X36 : $i]:
% 2.11/2.35         (((X36) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X36) @ X36))),
% 2.11/2.35      inference('cnf', [status(esa)], [t34_mcart_1])).
% 2.11/2.35  thf(d1_xboole_0, axiom,
% 2.11/2.35    (![A:$i]:
% 2.11/2.35     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 2.11/2.35  thf('8', plain,
% 2.11/2.35      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.11/2.35      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.11/2.35  thf('9', plain,
% 2.11/2.35      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.11/2.35      inference('sup-', [status(thm)], ['7', '8'])).
% 2.11/2.35  thf('10', plain,
% 2.11/2.35      ((((k4_tarski @ (sk_D_1 @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1))
% 2.11/2.35        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 2.11/2.35      inference('sup-', [status(thm)], ['6', '9'])).
% 2.11/2.35  thf('11', plain,
% 2.11/2.35      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.11/2.35         ((k3_zfmisc_1 @ X26 @ X27 @ X28)
% 2.11/2.35           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27) @ X28))),
% 2.11/2.35      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 2.11/2.35  thf(t113_zfmisc_1, axiom,
% 2.11/2.35    (![A:$i,B:$i]:
% 2.11/2.35     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 2.11/2.35       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 2.11/2.35  thf('12', plain,
% 2.11/2.35      (![X14 : $i, X15 : $i]:
% 2.11/2.35         (((X14) = (k1_xboole_0))
% 2.11/2.35          | ((X15) = (k1_xboole_0))
% 2.11/2.35          | ((k2_zfmisc_1 @ X15 @ X14) != (k1_xboole_0)))),
% 2.11/2.35      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.11/2.35  thf('13', plain,
% 2.11/2.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.11/2.35         (((k3_zfmisc_1 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 2.11/2.35          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 2.11/2.35          | ((X0) = (k1_xboole_0)))),
% 2.11/2.35      inference('sup-', [status(thm)], ['11', '12'])).
% 2.11/2.35  thf('14', plain,
% 2.11/2.35      ((((k1_xboole_0) != (k1_xboole_0))
% 2.11/2.35        | ((k4_tarski @ (sk_D_1 @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1))
% 2.11/2.35        | ((sk_C) = (k1_xboole_0))
% 2.11/2.35        | ((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0)))),
% 2.11/2.35      inference('sup-', [status(thm)], ['10', '13'])).
% 2.11/2.35  thf('15', plain,
% 2.11/2.35      ((((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 2.11/2.35        | ((sk_C) = (k1_xboole_0))
% 2.11/2.35        | ((k4_tarski @ (sk_D_1 @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1)))),
% 2.11/2.35      inference('simplify', [status(thm)], ['14'])).
% 2.11/2.35  thf('16', plain, (((sk_C) != (k1_xboole_0))),
% 2.11/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.35  thf('17', plain,
% 2.11/2.35      ((((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 2.11/2.35        | ((k4_tarski @ (sk_D_1 @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1)))),
% 2.11/2.35      inference('simplify_reflect-', [status(thm)], ['15', '16'])).
% 2.11/2.35  thf('18', plain,
% 2.11/2.35      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 2.11/2.35        | ((k4_tarski @ (sk_D_1 @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1)))),
% 2.11/2.35      inference('sup-', [status(thm)], ['2', '5'])).
% 2.11/2.35  thf('19', plain,
% 2.11/2.35      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.11/2.35         ((k3_zfmisc_1 @ X26 @ X27 @ X28)
% 2.11/2.35           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27) @ X28))),
% 2.11/2.35      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 2.11/2.35  thf('20', plain,
% 2.11/2.35      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.11/2.35      inference('sup-', [status(thm)], ['7', '8'])).
% 2.11/2.35  thf('21', plain,
% 2.11/2.35      (![X14 : $i, X15 : $i]:
% 2.11/2.35         (((X14) = (k1_xboole_0))
% 2.11/2.35          | ((X15) = (k1_xboole_0))
% 2.11/2.35          | ((k2_zfmisc_1 @ X15 @ X14) != (k1_xboole_0)))),
% 2.11/2.35      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.11/2.35  thf('22', plain,
% 2.11/2.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.11/2.35         (((k2_zfmisc_1 @ X2 @ X1) != (X0))
% 2.11/2.35          | ~ (v1_xboole_0 @ X0)
% 2.11/2.35          | ((X2) = (k1_xboole_0))
% 2.11/2.35          | ((X1) = (k1_xboole_0)))),
% 2.11/2.35      inference('sup-', [status(thm)], ['20', '21'])).
% 2.11/2.35  thf('23', plain,
% 2.11/2.35      (![X1 : $i, X2 : $i]:
% 2.11/2.35         (((X1) = (k1_xboole_0))
% 2.11/2.35          | ((X2) = (k1_xboole_0))
% 2.11/2.35          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1)))),
% 2.11/2.35      inference('simplify', [status(thm)], ['22'])).
% 2.11/2.35  thf('24', plain,
% 2.11/2.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.11/2.35         (~ (v1_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 2.11/2.35          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 2.11/2.35          | ((X0) = (k1_xboole_0)))),
% 2.11/2.35      inference('sup-', [status(thm)], ['19', '23'])).
% 2.11/2.35  thf('25', plain,
% 2.11/2.35      ((((k4_tarski @ (sk_D_1 @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1))
% 2.11/2.35        | ((sk_C) = (k1_xboole_0))
% 2.11/2.35        | ((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0)))),
% 2.11/2.35      inference('sup-', [status(thm)], ['18', '24'])).
% 2.11/2.35  thf('26', plain, (((sk_C) != (k1_xboole_0))),
% 2.11/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.35  thf('27', plain,
% 2.11/2.35      ((((k4_tarski @ (sk_D_1 @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1))
% 2.11/2.35        | ((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0)))),
% 2.11/2.35      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 2.11/2.35  thf(t7_mcart_1, axiom,
% 2.11/2.35    (![A:$i,B:$i]:
% 2.11/2.35     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 2.11/2.35       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 2.11/2.35  thf('28', plain,
% 2.11/2.35      (![X50 : $i, X51 : $i]: ((k1_mcart_1 @ (k4_tarski @ X50 @ X51)) = (X50))),
% 2.11/2.35      inference('cnf', [status(esa)], [t7_mcart_1])).
% 2.11/2.35  thf('29', plain,
% 2.11/2.35      ((((k1_mcart_1 @ sk_E_1) = (sk_D_1 @ sk_E_1))
% 2.11/2.35        | ((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0)))),
% 2.11/2.35      inference('sup+', [status(thm)], ['27', '28'])).
% 2.11/2.35  thf('30', plain,
% 2.11/2.35      (![X14 : $i, X15 : $i]:
% 2.11/2.35         (((X14) = (k1_xboole_0))
% 2.11/2.35          | ((X15) = (k1_xboole_0))
% 2.11/2.35          | ((k2_zfmisc_1 @ X15 @ X14) != (k1_xboole_0)))),
% 2.11/2.35      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.11/2.35  thf('31', plain,
% 2.11/2.35      ((((k1_xboole_0) != (k1_xboole_0))
% 2.11/2.35        | ((k1_mcart_1 @ sk_E_1) = (sk_D_1 @ sk_E_1))
% 2.11/2.35        | ((sk_A) = (k1_xboole_0))
% 2.11/2.35        | ((sk_B_2) = (k1_xboole_0)))),
% 2.11/2.35      inference('sup-', [status(thm)], ['29', '30'])).
% 2.11/2.35  thf('32', plain,
% 2.11/2.35      ((((sk_B_2) = (k1_xboole_0))
% 2.11/2.35        | ((sk_A) = (k1_xboole_0))
% 2.11/2.35        | ((k1_mcart_1 @ sk_E_1) = (sk_D_1 @ sk_E_1)))),
% 2.11/2.35      inference('simplify', [status(thm)], ['31'])).
% 2.11/2.35  thf('33', plain, (((sk_A) != (k1_xboole_0))),
% 2.11/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.35  thf('34', plain, (((sk_B_2) != (k1_xboole_0))),
% 2.11/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.35  thf('35', plain, (((k1_mcart_1 @ sk_E_1) = (sk_D_1 @ sk_E_1))),
% 2.11/2.35      inference('simplify_reflect-', [status(thm)], ['32', '33', '34'])).
% 2.11/2.35  thf('36', plain,
% 2.11/2.35      ((((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 2.11/2.35        | ((k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1)))),
% 2.11/2.35      inference('demod', [status(thm)], ['17', '35'])).
% 2.11/2.35  thf('37', plain,
% 2.11/2.35      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 2.11/2.35        | (r2_hidden @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 2.11/2.35      inference('sup-', [status(thm)], ['0', '1'])).
% 2.11/2.35  thf('38', plain,
% 2.11/2.35      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.11/2.35         ((k3_zfmisc_1 @ X26 @ X27 @ X28)
% 2.11/2.35           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27) @ X28))),
% 2.11/2.35      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 2.11/2.35  thf(t10_mcart_1, axiom,
% 2.11/2.35    (![A:$i,B:$i,C:$i]:
% 2.11/2.35     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 2.11/2.35       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 2.11/2.35         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 2.11/2.35  thf('39', plain,
% 2.11/2.35      (![X33 : $i, X34 : $i, X35 : $i]:
% 2.11/2.35         ((r2_hidden @ (k1_mcart_1 @ X33) @ X34)
% 2.11/2.35          | ~ (r2_hidden @ X33 @ (k2_zfmisc_1 @ X34 @ X35)))),
% 2.11/2.35      inference('cnf', [status(esa)], [t10_mcart_1])).
% 2.11/2.35  thf('40', plain,
% 2.11/2.35      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.11/2.35         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 2.11/2.35          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 2.11/2.35      inference('sup-', [status(thm)], ['38', '39'])).
% 2.11/2.35  thf('41', plain,
% 2.11/2.35      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 2.11/2.35        | (r2_hidden @ (k1_mcart_1 @ sk_E_1) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 2.11/2.35      inference('sup-', [status(thm)], ['37', '40'])).
% 2.11/2.35  thf('42', plain,
% 2.11/2.35      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.11/2.35         (((k4_tarski @ (sk_D_1 @ X11) @ (sk_E @ X11)) = (X11))
% 2.11/2.35          | ~ (r2_hidden @ X11 @ (k2_zfmisc_1 @ X12 @ X13)))),
% 2.11/2.35      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 2.11/2.35  thf('43', plain,
% 2.11/2.35      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 2.11/2.35        | ((k4_tarski @ (sk_D_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 2.11/2.35            (sk_E @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1)))),
% 2.11/2.35      inference('sup-', [status(thm)], ['41', '42'])).
% 2.11/2.35  thf('44', plain,
% 2.11/2.35      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 2.11/2.35        | ((k4_tarski @ (sk_D_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 2.11/2.35            (sk_E @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1)))),
% 2.11/2.35      inference('sup-', [status(thm)], ['41', '42'])).
% 2.11/2.35  thf('45', plain,
% 2.11/2.35      (![X50 : $i, X51 : $i]: ((k1_mcart_1 @ (k4_tarski @ X50 @ X51)) = (X50))),
% 2.11/2.35      inference('cnf', [status(esa)], [t7_mcart_1])).
% 2.11/2.35  thf('46', plain,
% 2.11/2.35      ((((k1_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 2.11/2.35          = (sk_D_1 @ (k1_mcart_1 @ sk_E_1)))
% 2.11/2.35        | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 2.11/2.35      inference('sup+', [status(thm)], ['44', '45'])).
% 2.11/2.35  thf('47', plain,
% 2.11/2.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.11/2.35         (~ (v1_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 2.11/2.35          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 2.11/2.35          | ((X0) = (k1_xboole_0)))),
% 2.11/2.35      inference('sup-', [status(thm)], ['19', '23'])).
% 2.11/2.35  thf('48', plain,
% 2.11/2.35      ((((k1_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 2.11/2.35          = (sk_D_1 @ (k1_mcart_1 @ sk_E_1)))
% 2.11/2.35        | ((sk_C) = (k1_xboole_0))
% 2.11/2.35        | ((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0)))),
% 2.11/2.35      inference('sup-', [status(thm)], ['46', '47'])).
% 2.11/2.35  thf('49', plain, (((sk_C) != (k1_xboole_0))),
% 2.11/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.35  thf('50', plain,
% 2.11/2.35      ((((k1_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 2.11/2.35          = (sk_D_1 @ (k1_mcart_1 @ sk_E_1)))
% 2.11/2.35        | ((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0)))),
% 2.11/2.35      inference('simplify_reflect-', [status(thm)], ['48', '49'])).
% 2.11/2.35  thf('51', plain,
% 2.11/2.35      (![X14 : $i, X15 : $i]:
% 2.11/2.35         (((X14) = (k1_xboole_0))
% 2.11/2.35          | ((X15) = (k1_xboole_0))
% 2.11/2.35          | ((k2_zfmisc_1 @ X15 @ X14) != (k1_xboole_0)))),
% 2.11/2.35      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.11/2.35  thf('52', plain,
% 2.11/2.35      ((((k1_xboole_0) != (k1_xboole_0))
% 2.11/2.35        | ((k1_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 2.11/2.35            = (sk_D_1 @ (k1_mcart_1 @ sk_E_1)))
% 2.11/2.35        | ((sk_A) = (k1_xboole_0))
% 2.11/2.35        | ((sk_B_2) = (k1_xboole_0)))),
% 2.11/2.35      inference('sup-', [status(thm)], ['50', '51'])).
% 2.11/2.35  thf('53', plain,
% 2.11/2.35      ((((sk_B_2) = (k1_xboole_0))
% 2.11/2.35        | ((sk_A) = (k1_xboole_0))
% 2.11/2.35        | ((k1_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 2.11/2.35            = (sk_D_1 @ (k1_mcart_1 @ sk_E_1))))),
% 2.11/2.35      inference('simplify', [status(thm)], ['52'])).
% 2.11/2.35  thf('54', plain, (((sk_A) != (k1_xboole_0))),
% 2.11/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.35  thf('55', plain, (((sk_B_2) != (k1_xboole_0))),
% 2.11/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.35  thf('56', plain,
% 2.11/2.35      (((k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) = (sk_D_1 @ (k1_mcart_1 @ sk_E_1)))),
% 2.11/2.35      inference('simplify_reflect-', [status(thm)], ['53', '54', '55'])).
% 2.11/2.35  thf('57', plain,
% 2.11/2.35      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 2.11/2.35        | ((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 2.11/2.35            (sk_E @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1)))),
% 2.11/2.35      inference('demod', [status(thm)], ['43', '56'])).
% 2.11/2.35  thf('58', plain,
% 2.11/2.35      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 2.11/2.35        | ((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 2.11/2.35            (sk_E @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1)))),
% 2.11/2.35      inference('demod', [status(thm)], ['43', '56'])).
% 2.11/2.35  thf('59', plain,
% 2.11/2.35      (![X50 : $i, X52 : $i]: ((k2_mcart_1 @ (k4_tarski @ X50 @ X52)) = (X52))),
% 2.11/2.35      inference('cnf', [status(esa)], [t7_mcart_1])).
% 2.11/2.35  thf('60', plain,
% 2.11/2.35      ((((k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) = (sk_E @ (k1_mcart_1 @ sk_E_1)))
% 2.11/2.35        | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 2.11/2.35      inference('sup+', [status(thm)], ['58', '59'])).
% 2.11/2.35  thf('61', plain,
% 2.11/2.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.11/2.35         (~ (v1_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 2.11/2.35          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 2.11/2.35          | ((X0) = (k1_xboole_0)))),
% 2.11/2.35      inference('sup-', [status(thm)], ['19', '23'])).
% 2.11/2.35  thf('62', plain,
% 2.11/2.35      ((((k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) = (sk_E @ (k1_mcart_1 @ sk_E_1)))
% 2.11/2.35        | ((sk_C) = (k1_xboole_0))
% 2.11/2.35        | ((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0)))),
% 2.11/2.35      inference('sup-', [status(thm)], ['60', '61'])).
% 2.11/2.35  thf('63', plain, (((sk_C) != (k1_xboole_0))),
% 2.11/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.35  thf('64', plain,
% 2.11/2.35      ((((k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) = (sk_E @ (k1_mcart_1 @ sk_E_1)))
% 2.11/2.35        | ((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0)))),
% 2.11/2.35      inference('simplify_reflect-', [status(thm)], ['62', '63'])).
% 2.11/2.35  thf('65', plain,
% 2.11/2.35      (![X14 : $i, X15 : $i]:
% 2.11/2.35         (((X14) = (k1_xboole_0))
% 2.11/2.35          | ((X15) = (k1_xboole_0))
% 2.11/2.35          | ((k2_zfmisc_1 @ X15 @ X14) != (k1_xboole_0)))),
% 2.11/2.35      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.11/2.35  thf('66', plain,
% 2.11/2.35      ((((k1_xboole_0) != (k1_xboole_0))
% 2.11/2.35        | ((k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 2.11/2.35            = (sk_E @ (k1_mcart_1 @ sk_E_1)))
% 2.11/2.35        | ((sk_A) = (k1_xboole_0))
% 2.11/2.35        | ((sk_B_2) = (k1_xboole_0)))),
% 2.11/2.35      inference('sup-', [status(thm)], ['64', '65'])).
% 2.11/2.35  thf('67', plain,
% 2.11/2.35      ((((sk_B_2) = (k1_xboole_0))
% 2.11/2.35        | ((sk_A) = (k1_xboole_0))
% 2.11/2.35        | ((k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))
% 2.11/2.35            = (sk_E @ (k1_mcart_1 @ sk_E_1))))),
% 2.11/2.35      inference('simplify', [status(thm)], ['66'])).
% 2.11/2.35  thf('68', plain, (((sk_A) != (k1_xboole_0))),
% 2.11/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.35  thf('69', plain, (((sk_B_2) != (k1_xboole_0))),
% 2.11/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.35  thf('70', plain,
% 2.11/2.35      (((k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) = (sk_E @ (k1_mcart_1 @ sk_E_1)))),
% 2.11/2.35      inference('simplify_reflect-', [status(thm)], ['67', '68', '69'])).
% 2.11/2.35  thf('71', plain,
% 2.11/2.35      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 2.11/2.35        | ((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 2.11/2.35            (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1)))),
% 2.11/2.35      inference('demod', [status(thm)], ['57', '70'])).
% 2.11/2.35  thf('72', plain,
% 2.11/2.35      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.11/2.35      inference('sup-', [status(thm)], ['7', '8'])).
% 2.11/2.35  thf('73', plain,
% 2.11/2.35      (![X15 : $i, X16 : $i]:
% 2.11/2.35         (((k2_zfmisc_1 @ X15 @ X16) = (k1_xboole_0))
% 2.11/2.35          | ((X15) != (k1_xboole_0)))),
% 2.11/2.35      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.11/2.35  thf('74', plain,
% 2.11/2.35      (![X16 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X16) = (k1_xboole_0))),
% 2.11/2.35      inference('simplify', [status(thm)], ['73'])).
% 2.11/2.35  thf('75', plain,
% 2.11/2.35      (![X0 : $i, X1 : $i]:
% 2.11/2.35         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.11/2.35      inference('sup+', [status(thm)], ['72', '74'])).
% 2.11/2.35  thf('76', plain,
% 2.11/2.35      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 2.11/2.35        | ((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 2.11/2.35            (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1)))),
% 2.11/2.35      inference('demod', [status(thm)], ['57', '70'])).
% 2.11/2.35  thf('77', plain,
% 2.11/2.35      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.11/2.35      inference('sup-', [status(thm)], ['7', '8'])).
% 2.11/2.35  thf('78', plain,
% 2.11/2.35      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.11/2.35      inference('sup-', [status(thm)], ['7', '8'])).
% 2.11/2.35  thf('79', plain,
% 2.11/2.35      (![X0 : $i, X1 : $i]:
% 2.11/2.35         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 2.11/2.35      inference('sup+', [status(thm)], ['77', '78'])).
% 2.11/2.35  thf('80', plain,
% 2.11/2.35      (![X0 : $i]:
% 2.11/2.35         (((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 2.11/2.35            (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1))
% 2.11/2.35          | ~ (v1_xboole_0 @ X0)
% 2.11/2.35          | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (X0)))),
% 2.11/2.35      inference('sup-', [status(thm)], ['76', '79'])).
% 2.11/2.35  thf(d4_zfmisc_1, axiom,
% 2.11/2.35    (![A:$i,B:$i,C:$i,D:$i]:
% 2.11/2.35     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 2.11/2.35       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 2.11/2.35  thf('81', plain,
% 2.11/2.35      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 2.11/2.35         ((k4_zfmisc_1 @ X29 @ X30 @ X31 @ X32)
% 2.11/2.35           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X29 @ X30 @ X31) @ X32))),
% 2.11/2.35      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 2.11/2.35  thf('82', plain,
% 2.11/2.35      (![X0 : $i, X1 : $i]:
% 2.11/2.35         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X1) = (k2_zfmisc_1 @ X0 @ X1))
% 2.11/2.35          | ~ (v1_xboole_0 @ X0)
% 2.11/2.35          | ((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 2.11/2.35              (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1)))),
% 2.11/2.35      inference('sup+', [status(thm)], ['80', '81'])).
% 2.11/2.35  thf('83', plain,
% 2.11/2.35      (![X0 : $i, X1 : $i]:
% 2.11/2.35         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0) = (k1_xboole_0))
% 2.11/2.35          | ~ (v1_xboole_0 @ X1)
% 2.11/2.35          | ((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 2.11/2.35              (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1))
% 2.11/2.35          | ~ (v1_xboole_0 @ X1))),
% 2.11/2.35      inference('sup+', [status(thm)], ['75', '82'])).
% 2.11/2.35  thf('84', plain,
% 2.11/2.35      (![X0 : $i, X1 : $i]:
% 2.11/2.35         (((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 2.11/2.35            (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1))
% 2.11/2.35          | ~ (v1_xboole_0 @ X1)
% 2.11/2.35          | ((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0) = (k1_xboole_0)))),
% 2.11/2.35      inference('simplify', [status(thm)], ['83'])).
% 2.11/2.35  thf('85', plain,
% 2.11/2.35      (![X0 : $i]:
% 2.11/2.35         (((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 2.11/2.35            (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1))
% 2.11/2.35          | ((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0) = (k1_xboole_0))
% 2.11/2.35          | ((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 2.11/2.35              (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1)))),
% 2.11/2.35      inference('sup-', [status(thm)], ['71', '84'])).
% 2.11/2.35  thf('86', plain,
% 2.11/2.35      (![X0 : $i]:
% 2.11/2.35         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0) = (k1_xboole_0))
% 2.11/2.35          | ((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 2.11/2.35              (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1)))),
% 2.11/2.35      inference('simplify', [status(thm)], ['85'])).
% 2.11/2.35  thf(t55_mcart_1, axiom,
% 2.11/2.35    (![A:$i,B:$i,C:$i,D:$i]:
% 2.11/2.35     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 2.11/2.35         ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) ) <=>
% 2.11/2.35       ( ( k4_zfmisc_1 @ A @ B @ C @ D ) != ( k1_xboole_0 ) ) ))).
% 2.11/2.35  thf('87', plain,
% 2.11/2.35      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 2.11/2.35         (((k4_zfmisc_1 @ X45 @ X46 @ X47 @ X48) != (k1_xboole_0))
% 2.11/2.35          | ((X48) = (k1_xboole_0))
% 2.11/2.35          | ((X47) = (k1_xboole_0))
% 2.11/2.35          | ((X46) = (k1_xboole_0))
% 2.11/2.35          | ((X45) = (k1_xboole_0)))),
% 2.11/2.35      inference('cnf', [status(esa)], [t55_mcart_1])).
% 2.11/2.35  thf('88', plain,
% 2.11/2.35      (![X0 : $i]:
% 2.11/2.35         (((k1_xboole_0) != (k1_xboole_0))
% 2.11/2.35          | ((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 2.11/2.35              (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1))
% 2.11/2.35          | ((sk_A) = (k1_xboole_0))
% 2.11/2.35          | ((sk_B_2) = (k1_xboole_0))
% 2.11/2.35          | ((sk_C) = (k1_xboole_0))
% 2.11/2.35          | ((X0) = (k1_xboole_0)))),
% 2.11/2.35      inference('sup-', [status(thm)], ['86', '87'])).
% 2.11/2.35  thf('89', plain,
% 2.11/2.35      (![X0 : $i]:
% 2.11/2.35         (((X0) = (k1_xboole_0))
% 2.11/2.35          | ((sk_C) = (k1_xboole_0))
% 2.11/2.35          | ((sk_B_2) = (k1_xboole_0))
% 2.11/2.35          | ((sk_A) = (k1_xboole_0))
% 2.11/2.35          | ((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 2.11/2.35              (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1)))),
% 2.11/2.35      inference('simplify', [status(thm)], ['88'])).
% 2.11/2.35  thf('90', plain, (((sk_A) != (k1_xboole_0))),
% 2.11/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.35  thf('91', plain, (((sk_B_2) != (k1_xboole_0))),
% 2.11/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.35  thf('92', plain, (((sk_C) != (k1_xboole_0))),
% 2.11/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.35  thf('93', plain,
% 2.11/2.35      (![X0 : $i]:
% 2.11/2.35         (((X0) = (k1_xboole_0))
% 2.11/2.35          | ((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 2.11/2.35              (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1)))),
% 2.11/2.35      inference('simplify_reflect-', [status(thm)], ['89', '90', '91', '92'])).
% 2.11/2.35  thf('94', plain,
% 2.11/2.35      (![X0 : $i]:
% 2.11/2.35         (((X0) = (k1_xboole_0))
% 2.11/2.35          | ((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 2.11/2.35              (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1)))),
% 2.11/2.35      inference('simplify_reflect-', [status(thm)], ['89', '90', '91', '92'])).
% 2.11/2.35  thf('95', plain,
% 2.11/2.35      (![X0 : $i, X1 : $i]:
% 2.11/2.35         (((X1) = (X0))
% 2.11/2.35          | ((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 2.11/2.35              (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1))
% 2.11/2.35          | ((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 2.11/2.35              (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1)))),
% 2.11/2.35      inference('sup+', [status(thm)], ['93', '94'])).
% 2.11/2.35  thf('96', plain,
% 2.11/2.35      (![X0 : $i, X1 : $i]:
% 2.11/2.35         (((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 2.11/2.35            (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1))
% 2.11/2.35          | ((X1) = (X0)))),
% 2.11/2.35      inference('simplify', [status(thm)], ['95'])).
% 2.11/2.35  thf('97', plain,
% 2.11/2.35      (((k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 2.11/2.35         (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1))) = (k1_mcart_1 @ sk_E_1))),
% 2.11/2.35      inference('condensation', [status(thm)], ['96'])).
% 2.11/2.35  thf(d3_mcart_1, axiom,
% 2.11/2.35    (![A:$i,B:$i,C:$i]:
% 2.11/2.35     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 2.11/2.35  thf('98', plain,
% 2.11/2.35      (![X23 : $i, X24 : $i, X25 : $i]:
% 2.11/2.35         ((k3_mcart_1 @ X23 @ X24 @ X25)
% 2.11/2.35           = (k4_tarski @ (k4_tarski @ X23 @ X24) @ X25))),
% 2.11/2.35      inference('cnf', [status(esa)], [d3_mcart_1])).
% 2.11/2.35  thf('99', plain,
% 2.11/2.35      (![X0 : $i]:
% 2.11/2.35         ((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ 
% 2.11/2.35           (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ X0)
% 2.11/2.35           = (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ X0))),
% 2.11/2.35      inference('sup+', [status(thm)], ['97', '98'])).
% 2.11/2.35  thf('100', plain,
% 2.11/2.35      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 2.11/2.35        | (r2_hidden @ (k1_mcart_1 @ sk_E_1) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 2.11/2.35      inference('sup-', [status(thm)], ['37', '40'])).
% 2.11/2.35  thf('101', plain,
% 2.11/2.35      (![X33 : $i, X34 : $i, X35 : $i]:
% 2.11/2.35         ((r2_hidden @ (k2_mcart_1 @ X33) @ X35)
% 2.11/2.35          | ~ (r2_hidden @ X33 @ (k2_zfmisc_1 @ X34 @ X35)))),
% 2.11/2.35      inference('cnf', [status(esa)], [t10_mcart_1])).
% 2.11/2.35  thf('102', plain,
% 2.11/2.35      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 2.11/2.35        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_2))),
% 2.11/2.35      inference('sup-', [status(thm)], ['100', '101'])).
% 2.11/2.35  thf('103', plain,
% 2.11/2.35      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.11/2.35      inference('sup-', [status(thm)], ['7', '8'])).
% 2.11/2.35  thf('104', plain,
% 2.11/2.35      (((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_2)
% 2.11/2.35        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 2.11/2.35      inference('sup-', [status(thm)], ['102', '103'])).
% 2.11/2.35  thf('105', plain,
% 2.11/2.35      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 2.11/2.35         ((k4_zfmisc_1 @ X29 @ X30 @ X31 @ X32)
% 2.11/2.35           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X29 @ X30 @ X31) @ X32))),
% 2.11/2.35      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 2.11/2.35  thf('106', plain,
% 2.11/2.35      (![X0 : $i]:
% 2.11/2.35         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0)
% 2.11/2.35            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 2.11/2.35          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_2))),
% 2.11/2.35      inference('sup+', [status(thm)], ['104', '105'])).
% 2.11/2.35  thf('107', plain,
% 2.11/2.35      (![X16 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X16) = (k1_xboole_0))),
% 2.11/2.35      inference('simplify', [status(thm)], ['73'])).
% 2.11/2.35  thf('108', plain,
% 2.11/2.35      (![X0 : $i]:
% 2.11/2.35         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0) = (k1_xboole_0))
% 2.11/2.35          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_2))),
% 2.11/2.35      inference('demod', [status(thm)], ['106', '107'])).
% 2.11/2.35  thf('109', plain,
% 2.11/2.35      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 2.11/2.35         (((k4_zfmisc_1 @ X45 @ X46 @ X47 @ X48) != (k1_xboole_0))
% 2.11/2.35          | ((X48) = (k1_xboole_0))
% 2.11/2.35          | ((X47) = (k1_xboole_0))
% 2.11/2.35          | ((X46) = (k1_xboole_0))
% 2.11/2.35          | ((X45) = (k1_xboole_0)))),
% 2.11/2.35      inference('cnf', [status(esa)], [t55_mcart_1])).
% 2.11/2.35  thf('110', plain,
% 2.11/2.35      (![X0 : $i]:
% 2.11/2.35         (((k1_xboole_0) != (k1_xboole_0))
% 2.11/2.35          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_2)
% 2.11/2.35          | ((sk_A) = (k1_xboole_0))
% 2.11/2.35          | ((sk_B_2) = (k1_xboole_0))
% 2.11/2.35          | ((sk_C) = (k1_xboole_0))
% 2.11/2.35          | ((X0) = (k1_xboole_0)))),
% 2.11/2.35      inference('sup-', [status(thm)], ['108', '109'])).
% 2.11/2.35  thf('111', plain,
% 2.11/2.35      (![X0 : $i]:
% 2.11/2.35         (((X0) = (k1_xboole_0))
% 2.11/2.35          | ((sk_C) = (k1_xboole_0))
% 2.11/2.35          | ((sk_B_2) = (k1_xboole_0))
% 2.11/2.35          | ((sk_A) = (k1_xboole_0))
% 2.11/2.35          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_2))),
% 2.11/2.35      inference('simplify', [status(thm)], ['110'])).
% 2.11/2.35  thf('112', plain, (((sk_A) != (k1_xboole_0))),
% 2.11/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.35  thf('113', plain, (((sk_B_2) != (k1_xboole_0))),
% 2.11/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.35  thf('114', plain, (((sk_C) != (k1_xboole_0))),
% 2.11/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.35  thf('115', plain,
% 2.11/2.35      (![X0 : $i]:
% 2.11/2.35         (((X0) = (k1_xboole_0))
% 2.11/2.35          | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_2))),
% 2.11/2.35      inference('simplify_reflect-', [status(thm)],
% 2.11/2.35                ['111', '112', '113', '114'])).
% 2.11/2.35  thf(t1_subset, axiom,
% 2.11/2.35    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 2.11/2.35  thf('116', plain,
% 2.11/2.35      (![X19 : $i, X20 : $i]:
% 2.11/2.35         ((m1_subset_1 @ X19 @ X20) | ~ (r2_hidden @ X19 @ X20))),
% 2.11/2.35      inference('cnf', [status(esa)], [t1_subset])).
% 2.11/2.35  thf('117', plain,
% 2.11/2.35      (![X0 : $i]:
% 2.11/2.35         (((X0) = (k1_xboole_0))
% 2.11/2.35          | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_2))),
% 2.11/2.35      inference('sup-', [status(thm)], ['115', '116'])).
% 2.11/2.35  thf('118', plain,
% 2.11/2.35      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.11/2.35      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.11/2.35  thf('119', plain,
% 2.11/2.35      (![X15 : $i, X16 : $i]:
% 2.11/2.35         (((k2_zfmisc_1 @ X15 @ X16) = (k1_xboole_0))
% 2.11/2.35          | ((X16) != (k1_xboole_0)))),
% 2.11/2.35      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.11/2.35  thf('120', plain,
% 2.11/2.35      (![X15 : $i]: ((k2_zfmisc_1 @ X15 @ k1_xboole_0) = (k1_xboole_0))),
% 2.11/2.35      inference('simplify', [status(thm)], ['119'])).
% 2.11/2.35  thf(t152_zfmisc_1, axiom,
% 2.11/2.35    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 2.11/2.35  thf('121', plain,
% 2.11/2.35      (![X17 : $i, X18 : $i]: ~ (r2_hidden @ X17 @ (k2_zfmisc_1 @ X17 @ X18))),
% 2.11/2.35      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 2.11/2.35  thf('122', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 2.11/2.35      inference('sup-', [status(thm)], ['120', '121'])).
% 2.11/2.35  thf('123', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.11/2.35      inference('sup-', [status(thm)], ['118', '122'])).
% 2.11/2.35  thf('124', plain,
% 2.11/2.35      (![X0 : $i]:
% 2.11/2.35         ((v1_xboole_0 @ X0)
% 2.11/2.35          | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_2))),
% 2.11/2.35      inference('sup+', [status(thm)], ['117', '123'])).
% 2.11/2.35  thf(d2_tarski, axiom,
% 2.11/2.35    (![A:$i,B:$i,C:$i]:
% 2.11/2.35     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 2.11/2.35       ( ![D:$i]:
% 2.11/2.35         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 2.11/2.35  thf('125', plain,
% 2.11/2.35      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 2.11/2.35         (((X4) != (X3))
% 2.11/2.35          | (r2_hidden @ X4 @ X5)
% 2.11/2.35          | ((X5) != (k2_tarski @ X6 @ X3)))),
% 2.11/2.35      inference('cnf', [status(esa)], [d2_tarski])).
% 2.11/2.35  thf('126', plain,
% 2.11/2.35      (![X3 : $i, X6 : $i]: (r2_hidden @ X3 @ (k2_tarski @ X6 @ X3))),
% 2.11/2.35      inference('simplify', [status(thm)], ['125'])).
% 2.11/2.35  thf('127', plain,
% 2.11/2.35      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.11/2.35      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.11/2.35  thf('128', plain,
% 2.11/2.35      (![X0 : $i, X1 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X1 @ X0))),
% 2.11/2.35      inference('sup-', [status(thm)], ['126', '127'])).
% 2.11/2.35  thf('129', plain,
% 2.11/2.35      ((m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_B_2)),
% 2.11/2.35      inference('sup-', [status(thm)], ['124', '128'])).
% 2.11/2.35  thf('130', plain,
% 2.11/2.35      (![X53 : $i, X54 : $i, X55 : $i]:
% 2.11/2.35         (~ (m1_subset_1 @ X53 @ sk_B_2)
% 2.11/2.35          | ((sk_E_1) != (k3_mcart_1 @ X54 @ X53 @ X55))
% 2.11/2.35          | ((sk_D_2) = (X55))
% 2.11/2.35          | ~ (m1_subset_1 @ X55 @ sk_C)
% 2.11/2.35          | ~ (m1_subset_1 @ X54 @ sk_A))),
% 2.11/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.35  thf('131', plain,
% 2.11/2.35      (![X0 : $i, X1 : $i]:
% 2.11/2.35         (~ (m1_subset_1 @ X0 @ sk_A)
% 2.11/2.35          | ~ (m1_subset_1 @ X1 @ sk_C)
% 2.11/2.35          | ((sk_D_2) = (X1))
% 2.11/2.35          | ((sk_E_1)
% 2.11/2.35              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ X1)))),
% 2.11/2.35      inference('sup-', [status(thm)], ['129', '130'])).
% 2.11/2.35  thf('132', plain,
% 2.11/2.35      (![X0 : $i]:
% 2.11/2.35         (((sk_E_1) != (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ X0))
% 2.11/2.35          | ((sk_D_2) = (X0))
% 2.11/2.35          | ~ (m1_subset_1 @ X0 @ sk_C)
% 2.11/2.35          | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A))),
% 2.11/2.35      inference('sup-', [status(thm)], ['99', '131'])).
% 2.11/2.35  thf('133', plain,
% 2.11/2.35      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 2.11/2.35        | (r2_hidden @ (k1_mcart_1 @ sk_E_1) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 2.11/2.35      inference('sup-', [status(thm)], ['37', '40'])).
% 2.11/2.35  thf('134', plain,
% 2.11/2.35      (![X33 : $i, X34 : $i, X35 : $i]:
% 2.11/2.35         ((r2_hidden @ (k1_mcart_1 @ X33) @ X34)
% 2.11/2.35          | ~ (r2_hidden @ X33 @ (k2_zfmisc_1 @ X34 @ X35)))),
% 2.11/2.35      inference('cnf', [status(esa)], [t10_mcart_1])).
% 2.11/2.35  thf('135', plain,
% 2.11/2.35      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 2.11/2.35        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A))),
% 2.11/2.35      inference('sup-', [status(thm)], ['133', '134'])).
% 2.11/2.35  thf('136', plain,
% 2.11/2.35      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.11/2.35      inference('sup-', [status(thm)], ['7', '8'])).
% 2.11/2.35  thf('137', plain,
% 2.11/2.35      (((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A)
% 2.11/2.35        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 2.11/2.35      inference('sup-', [status(thm)], ['135', '136'])).
% 2.11/2.35  thf('138', plain,
% 2.11/2.35      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 2.11/2.35         ((k4_zfmisc_1 @ X29 @ X30 @ X31 @ X32)
% 2.11/2.35           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X29 @ X30 @ X31) @ X32))),
% 2.11/2.35      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 2.11/2.35  thf('139', plain,
% 2.11/2.35      (![X0 : $i]:
% 2.11/2.35         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0)
% 2.11/2.35            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 2.11/2.35          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A))),
% 2.11/2.35      inference('sup+', [status(thm)], ['137', '138'])).
% 2.11/2.35  thf('140', plain,
% 2.11/2.35      (![X16 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X16) = (k1_xboole_0))),
% 2.11/2.35      inference('simplify', [status(thm)], ['73'])).
% 2.11/2.35  thf('141', plain,
% 2.11/2.35      (![X0 : $i]:
% 2.11/2.35         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0) = (k1_xboole_0))
% 2.11/2.35          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A))),
% 2.11/2.35      inference('demod', [status(thm)], ['139', '140'])).
% 2.11/2.35  thf('142', plain,
% 2.11/2.35      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 2.11/2.35         (((k4_zfmisc_1 @ X45 @ X46 @ X47 @ X48) != (k1_xboole_0))
% 2.11/2.35          | ((X48) = (k1_xboole_0))
% 2.11/2.35          | ((X47) = (k1_xboole_0))
% 2.11/2.35          | ((X46) = (k1_xboole_0))
% 2.11/2.35          | ((X45) = (k1_xboole_0)))),
% 2.11/2.35      inference('cnf', [status(esa)], [t55_mcart_1])).
% 2.11/2.35  thf('143', plain,
% 2.11/2.35      (![X0 : $i]:
% 2.11/2.35         (((k1_xboole_0) != (k1_xboole_0))
% 2.11/2.35          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A)
% 2.11/2.35          | ((sk_A) = (k1_xboole_0))
% 2.11/2.35          | ((sk_B_2) = (k1_xboole_0))
% 2.11/2.35          | ((sk_C) = (k1_xboole_0))
% 2.11/2.35          | ((X0) = (k1_xboole_0)))),
% 2.11/2.35      inference('sup-', [status(thm)], ['141', '142'])).
% 2.11/2.35  thf('144', plain,
% 2.11/2.35      (![X0 : $i]:
% 2.11/2.35         (((X0) = (k1_xboole_0))
% 2.11/2.35          | ((sk_C) = (k1_xboole_0))
% 2.11/2.35          | ((sk_B_2) = (k1_xboole_0))
% 2.11/2.35          | ((sk_A) = (k1_xboole_0))
% 2.11/2.35          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A))),
% 2.11/2.35      inference('simplify', [status(thm)], ['143'])).
% 2.11/2.35  thf('145', plain, (((sk_A) != (k1_xboole_0))),
% 2.11/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.35  thf('146', plain, (((sk_B_2) != (k1_xboole_0))),
% 2.11/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.35  thf('147', plain, (((sk_C) != (k1_xboole_0))),
% 2.11/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.35  thf('148', plain,
% 2.11/2.35      (![X0 : $i]:
% 2.11/2.35         (((X0) = (k1_xboole_0))
% 2.11/2.35          | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A))),
% 2.11/2.35      inference('simplify_reflect-', [status(thm)],
% 2.11/2.35                ['144', '145', '146', '147'])).
% 2.11/2.35  thf('149', plain,
% 2.11/2.35      (![X19 : $i, X20 : $i]:
% 2.11/2.35         ((m1_subset_1 @ X19 @ X20) | ~ (r2_hidden @ X19 @ X20))),
% 2.11/2.35      inference('cnf', [status(esa)], [t1_subset])).
% 2.11/2.35  thf('150', plain,
% 2.11/2.35      (![X0 : $i]:
% 2.11/2.35         (((X0) = (k1_xboole_0))
% 2.11/2.35          | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A))),
% 2.11/2.35      inference('sup-', [status(thm)], ['148', '149'])).
% 2.11/2.35  thf('151', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.11/2.35      inference('sup-', [status(thm)], ['118', '122'])).
% 2.11/2.35  thf('152', plain,
% 2.11/2.35      (![X0 : $i]:
% 2.11/2.35         ((v1_xboole_0 @ X0)
% 2.11/2.35          | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A))),
% 2.11/2.35      inference('sup+', [status(thm)], ['150', '151'])).
% 2.11/2.35  thf('153', plain,
% 2.11/2.35      (![X0 : $i, X1 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X1 @ X0))),
% 2.11/2.35      inference('sup-', [status(thm)], ['126', '127'])).
% 2.11/2.35  thf('154', plain,
% 2.11/2.35      ((m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E_1)) @ sk_A)),
% 2.11/2.35      inference('sup-', [status(thm)], ['152', '153'])).
% 2.11/2.35  thf('155', plain,
% 2.11/2.35      (![X0 : $i]:
% 2.11/2.35         (((sk_E_1) != (k4_tarski @ (k1_mcart_1 @ sk_E_1) @ X0))
% 2.11/2.35          | ((sk_D_2) = (X0))
% 2.11/2.35          | ~ (m1_subset_1 @ X0 @ sk_C))),
% 2.11/2.35      inference('demod', [status(thm)], ['132', '154'])).
% 2.11/2.35  thf('156', plain,
% 2.11/2.35      ((((sk_E_1) != (sk_E_1))
% 2.11/2.35        | ((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 2.11/2.35        | ~ (m1_subset_1 @ (sk_E @ sk_E_1) @ sk_C)
% 2.11/2.35        | ((sk_D_2) = (sk_E @ sk_E_1)))),
% 2.11/2.35      inference('sup-', [status(thm)], ['36', '155'])).
% 2.11/2.35  thf('157', plain,
% 2.11/2.35      ((((sk_D_2) = (sk_E @ sk_E_1))
% 2.11/2.35        | ~ (m1_subset_1 @ (sk_E @ sk_E_1) @ sk_C)
% 2.11/2.35        | ((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0)))),
% 2.11/2.35      inference('simplify', [status(thm)], ['156'])).
% 2.11/2.35  thf('158', plain,
% 2.11/2.35      ((((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 2.11/2.35        | ((k4_tarski @ (k1_mcart_1 @ sk_E_1) @ (sk_E @ sk_E_1)) = (sk_E_1)))),
% 2.11/2.35      inference('demod', [status(thm)], ['17', '35'])).
% 2.11/2.35  thf('159', plain,
% 2.11/2.35      (![X50 : $i, X52 : $i]: ((k2_mcart_1 @ (k4_tarski @ X50 @ X52)) = (X52))),
% 2.11/2.35      inference('cnf', [status(esa)], [t7_mcart_1])).
% 2.11/2.35  thf('160', plain,
% 2.11/2.35      ((((k2_mcart_1 @ sk_E_1) = (sk_E @ sk_E_1))
% 2.11/2.35        | ((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0)))),
% 2.11/2.35      inference('sup+', [status(thm)], ['158', '159'])).
% 2.11/2.35  thf('161', plain,
% 2.11/2.35      (![X14 : $i, X15 : $i]:
% 2.11/2.35         (((X14) = (k1_xboole_0))
% 2.11/2.35          | ((X15) = (k1_xboole_0))
% 2.11/2.35          | ((k2_zfmisc_1 @ X15 @ X14) != (k1_xboole_0)))),
% 2.11/2.35      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.11/2.35  thf('162', plain,
% 2.11/2.35      ((((k1_xboole_0) != (k1_xboole_0))
% 2.11/2.35        | ((k2_mcart_1 @ sk_E_1) = (sk_E @ sk_E_1))
% 2.11/2.35        | ((sk_A) = (k1_xboole_0))
% 2.11/2.35        | ((sk_B_2) = (k1_xboole_0)))),
% 2.11/2.35      inference('sup-', [status(thm)], ['160', '161'])).
% 2.11/2.35  thf('163', plain,
% 2.11/2.35      ((((sk_B_2) = (k1_xboole_0))
% 2.11/2.35        | ((sk_A) = (k1_xboole_0))
% 2.11/2.35        | ((k2_mcart_1 @ sk_E_1) = (sk_E @ sk_E_1)))),
% 2.11/2.35      inference('simplify', [status(thm)], ['162'])).
% 2.11/2.35  thf('164', plain, (((sk_A) != (k1_xboole_0))),
% 2.11/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.35  thf('165', plain, (((sk_B_2) != (k1_xboole_0))),
% 2.11/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.35  thf('166', plain, (((k2_mcart_1 @ sk_E_1) = (sk_E @ sk_E_1))),
% 2.11/2.35      inference('simplify_reflect-', [status(thm)], ['163', '164', '165'])).
% 2.11/2.35  thf('167', plain, (((k2_mcart_1 @ sk_E_1) = (sk_E @ sk_E_1))),
% 2.11/2.35      inference('simplify_reflect-', [status(thm)], ['163', '164', '165'])).
% 2.11/2.35  thf('168', plain,
% 2.11/2.35      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 2.11/2.35        | (r2_hidden @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C)))),
% 2.11/2.35      inference('sup-', [status(thm)], ['0', '1'])).
% 2.11/2.35  thf('169', plain,
% 2.11/2.35      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.11/2.35         ((k3_zfmisc_1 @ X26 @ X27 @ X28)
% 2.11/2.35           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27) @ X28))),
% 2.11/2.35      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 2.11/2.35  thf('170', plain,
% 2.11/2.35      (![X33 : $i, X34 : $i, X35 : $i]:
% 2.11/2.35         ((r2_hidden @ (k2_mcart_1 @ X33) @ X35)
% 2.11/2.35          | ~ (r2_hidden @ X33 @ (k2_zfmisc_1 @ X34 @ X35)))),
% 2.11/2.35      inference('cnf', [status(esa)], [t10_mcart_1])).
% 2.11/2.35  thf('171', plain,
% 2.11/2.35      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.11/2.35         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 2.11/2.35          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 2.11/2.35      inference('sup-', [status(thm)], ['169', '170'])).
% 2.11/2.35  thf('172', plain,
% 2.11/2.35      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))
% 2.11/2.35        | (r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C))),
% 2.11/2.35      inference('sup-', [status(thm)], ['168', '171'])).
% 2.11/2.35  thf('173', plain,
% 2.11/2.35      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.11/2.35      inference('sup-', [status(thm)], ['7', '8'])).
% 2.11/2.35  thf('174', plain,
% 2.11/2.35      (((r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C)
% 2.11/2.35        | ((k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C) = (k1_xboole_0)))),
% 2.11/2.35      inference('sup-', [status(thm)], ['172', '173'])).
% 2.11/2.35  thf('175', plain,
% 2.11/2.35      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 2.11/2.35         ((k4_zfmisc_1 @ X29 @ X30 @ X31 @ X32)
% 2.11/2.35           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X29 @ X30 @ X31) @ X32))),
% 2.11/2.35      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 2.11/2.35  thf('176', plain,
% 2.11/2.35      (![X0 : $i]:
% 2.11/2.35         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0)
% 2.11/2.35            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 2.11/2.35          | (r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C))),
% 2.11/2.35      inference('sup+', [status(thm)], ['174', '175'])).
% 2.11/2.35  thf('177', plain,
% 2.11/2.35      (![X16 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X16) = (k1_xboole_0))),
% 2.11/2.35      inference('simplify', [status(thm)], ['73'])).
% 2.11/2.35  thf('178', plain,
% 2.11/2.35      (![X0 : $i]:
% 2.11/2.35         (((k4_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C @ X0) = (k1_xboole_0))
% 2.11/2.35          | (r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C))),
% 2.11/2.35      inference('demod', [status(thm)], ['176', '177'])).
% 2.11/2.35  thf('179', plain,
% 2.11/2.35      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 2.11/2.35         (((k4_zfmisc_1 @ X45 @ X46 @ X47 @ X48) != (k1_xboole_0))
% 2.11/2.35          | ((X48) = (k1_xboole_0))
% 2.11/2.35          | ((X47) = (k1_xboole_0))
% 2.11/2.35          | ((X46) = (k1_xboole_0))
% 2.11/2.35          | ((X45) = (k1_xboole_0)))),
% 2.11/2.35      inference('cnf', [status(esa)], [t55_mcart_1])).
% 2.11/2.35  thf('180', plain,
% 2.11/2.35      (![X0 : $i]:
% 2.11/2.35         (((k1_xboole_0) != (k1_xboole_0))
% 2.11/2.35          | (r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C)
% 2.11/2.35          | ((sk_A) = (k1_xboole_0))
% 2.11/2.35          | ((sk_B_2) = (k1_xboole_0))
% 2.11/2.35          | ((sk_C) = (k1_xboole_0))
% 2.11/2.35          | ((X0) = (k1_xboole_0)))),
% 2.11/2.35      inference('sup-', [status(thm)], ['178', '179'])).
% 2.11/2.35  thf('181', plain,
% 2.11/2.35      (![X0 : $i]:
% 2.11/2.35         (((X0) = (k1_xboole_0))
% 2.11/2.35          | ((sk_C) = (k1_xboole_0))
% 2.11/2.35          | ((sk_B_2) = (k1_xboole_0))
% 2.11/2.35          | ((sk_A) = (k1_xboole_0))
% 2.11/2.35          | (r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C))),
% 2.11/2.35      inference('simplify', [status(thm)], ['180'])).
% 2.11/2.35  thf('182', plain, (((sk_A) != (k1_xboole_0))),
% 2.11/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.35  thf('183', plain, (((sk_B_2) != (k1_xboole_0))),
% 2.11/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.35  thf('184', plain, (((sk_C) != (k1_xboole_0))),
% 2.11/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.35  thf('185', plain,
% 2.11/2.35      (![X0 : $i]:
% 2.11/2.35         (((X0) = (k1_xboole_0)) | (r2_hidden @ (k2_mcart_1 @ sk_E_1) @ sk_C))),
% 2.11/2.35      inference('simplify_reflect-', [status(thm)],
% 2.11/2.35                ['181', '182', '183', '184'])).
% 2.11/2.35  thf('186', plain,
% 2.11/2.35      (![X19 : $i, X20 : $i]:
% 2.11/2.35         ((m1_subset_1 @ X19 @ X20) | ~ (r2_hidden @ X19 @ X20))),
% 2.11/2.35      inference('cnf', [status(esa)], [t1_subset])).
% 2.11/2.35  thf('187', plain,
% 2.11/2.35      (![X0 : $i]:
% 2.11/2.35         (((X0) = (k1_xboole_0)) | (m1_subset_1 @ (k2_mcart_1 @ sk_E_1) @ sk_C))),
% 2.11/2.35      inference('sup-', [status(thm)], ['185', '186'])).
% 2.11/2.35  thf('188', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.11/2.35      inference('sup-', [status(thm)], ['118', '122'])).
% 2.11/2.35  thf('189', plain,
% 2.11/2.35      (![X0 : $i]:
% 2.11/2.35         ((v1_xboole_0 @ X0) | (m1_subset_1 @ (k2_mcart_1 @ sk_E_1) @ sk_C))),
% 2.11/2.35      inference('sup+', [status(thm)], ['187', '188'])).
% 2.11/2.35  thf('190', plain,
% 2.11/2.35      (![X0 : $i, X1 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X1 @ X0))),
% 2.11/2.35      inference('sup-', [status(thm)], ['126', '127'])).
% 2.11/2.35  thf('191', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_E_1) @ sk_C)),
% 2.11/2.35      inference('sup-', [status(thm)], ['189', '190'])).
% 2.11/2.35  thf('192', plain,
% 2.11/2.35      ((((sk_D_2) = (k2_mcart_1 @ sk_E_1))
% 2.11/2.35        | ((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0)))),
% 2.11/2.35      inference('demod', [status(thm)], ['157', '166', '167', '191'])).
% 2.11/2.35  thf('193', plain,
% 2.11/2.35      (((sk_D_2) != (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_1))),
% 2.11/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.35  thf('194', plain,
% 2.11/2.35      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 2.11/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.35  thf(t50_mcart_1, axiom,
% 2.11/2.35    (![A:$i,B:$i,C:$i]:
% 2.11/2.35     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 2.11/2.35          ( ( C ) != ( k1_xboole_0 ) ) & 
% 2.11/2.35          ( ~( ![D:$i]:
% 2.11/2.35               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 2.11/2.35                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 2.11/2.35                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 2.11/2.35                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 2.11/2.35                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 2.11/2.35                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 2.11/2.35  thf('195', plain,
% 2.11/2.35      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 2.11/2.35         (((X41) = (k1_xboole_0))
% 2.11/2.35          | ((X42) = (k1_xboole_0))
% 2.11/2.35          | ((k7_mcart_1 @ X41 @ X42 @ X44 @ X43) = (k2_mcart_1 @ X43))
% 2.11/2.35          | ~ (m1_subset_1 @ X43 @ (k3_zfmisc_1 @ X41 @ X42 @ X44))
% 2.11/2.35          | ((X44) = (k1_xboole_0)))),
% 2.11/2.35      inference('cnf', [status(esa)], [t50_mcart_1])).
% 2.11/2.35  thf('196', plain,
% 2.11/2.35      ((((sk_C) = (k1_xboole_0))
% 2.11/2.35        | ((k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_1) = (k2_mcart_1 @ sk_E_1))
% 2.11/2.35        | ((sk_B_2) = (k1_xboole_0))
% 2.11/2.35        | ((sk_A) = (k1_xboole_0)))),
% 2.11/2.35      inference('sup-', [status(thm)], ['194', '195'])).
% 2.11/2.35  thf('197', plain, (((sk_A) != (k1_xboole_0))),
% 2.11/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.35  thf('198', plain, (((sk_B_2) != (k1_xboole_0))),
% 2.11/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.35  thf('199', plain, (((sk_C) != (k1_xboole_0))),
% 2.11/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.35  thf('200', plain,
% 2.11/2.35      (((k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_E_1) = (k2_mcart_1 @ sk_E_1))),
% 2.11/2.35      inference('simplify_reflect-', [status(thm)],
% 2.11/2.35                ['196', '197', '198', '199'])).
% 2.11/2.35  thf('201', plain, (((sk_D_2) != (k2_mcart_1 @ sk_E_1))),
% 2.11/2.35      inference('demod', [status(thm)], ['193', '200'])).
% 2.11/2.35  thf('202', plain, (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))),
% 2.11/2.35      inference('simplify_reflect-', [status(thm)], ['192', '201'])).
% 2.11/2.35  thf('203', plain,
% 2.11/2.35      (![X14 : $i, X15 : $i]:
% 2.11/2.35         (((X14) = (k1_xboole_0))
% 2.11/2.35          | ((X15) = (k1_xboole_0))
% 2.11/2.35          | ((k2_zfmisc_1 @ X15 @ X14) != (k1_xboole_0)))),
% 2.11/2.35      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.11/2.35  thf('204', plain,
% 2.11/2.35      ((((k1_xboole_0) != (k1_xboole_0))
% 2.11/2.35        | ((sk_A) = (k1_xboole_0))
% 2.11/2.35        | ((sk_B_2) = (k1_xboole_0)))),
% 2.11/2.35      inference('sup-', [status(thm)], ['202', '203'])).
% 2.11/2.35  thf('205', plain, ((((sk_B_2) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 2.11/2.35      inference('simplify', [status(thm)], ['204'])).
% 2.11/2.35  thf('206', plain, (((sk_A) != (k1_xboole_0))),
% 2.11/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.35  thf('207', plain, (((sk_B_2) != (k1_xboole_0))),
% 2.11/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.35  thf('208', plain, ($false),
% 2.11/2.35      inference('simplify_reflect-', [status(thm)], ['205', '206', '207'])).
% 2.11/2.35  
% 2.11/2.35  % SZS output end Refutation
% 2.11/2.35  
% 2.11/2.36  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
