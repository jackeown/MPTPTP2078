%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wYec5xRyo8

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:53 EST 2020

% Result     : Theorem 1.76s
% Output     : Refutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 167 expanded)
%              Number of leaves         :   31 (  61 expanded)
%              Depth                    :   19
%              Number of atoms          : 1055 (3106 expanded)
%              Number of equality atoms :  131 ( 439 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_zfmisc_1 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) @ X13 ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( X29 = k1_xboole_0 )
      | ( X30
        = ( k4_tarski @ ( k1_mcart_1 @ X30 ) @ ( k2_mcart_1 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k2_zfmisc_1 @ X29 @ X31 ) )
      | ( X31 = k1_xboole_0 ) ) ),
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

thf('7',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_zfmisc_1 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('11',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X26 ) @ X27 )
      | ~ ( r2_hidden @ X26 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('15',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( m1_subset_1 @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( X29 = k1_xboole_0 )
      | ( X30
        = ( k4_tarski @ ( k1_mcart_1 @ X30 ) @ ( k2_mcart_1 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k2_zfmisc_1 @ X29 @ X31 ) )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t24_mcart_1])).

thf('17',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( sk_B = k1_xboole_0 )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['17','18','19'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('21',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_mcart_1 @ X8 @ X9 @ X10 )
      = ( k4_tarski @ ( k4_tarski @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X0 )
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k6_mcart_1 @ A @ B @ C @ D ) @ B ) ) )).

thf('24',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( m1_subset_1 @ ( k6_mcart_1 @ X18 @ X19 @ X20 @ X21 ) @ X19 )
      | ~ ( m1_subset_1 @ X21 @ ( k3_zfmisc_1 @ X18 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_mcart_1])).

thf('25',plain,(
    m1_subset_1 @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_B ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X36 @ sk_B )
      | ( sk_D = X36 )
      | ( sk_E
       != ( k3_mcart_1 @ X37 @ X36 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ sk_C )
      | ~ ( m1_subset_1 @ X37 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_E
       != ( k3_mcart_1 @ X0 @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ X1 ) )
      | ( sk_D
        = ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    sk_D
 != ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_E
       != ( k3_mcart_1 @ X0 @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ X1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['27','28'])).

thf('30',plain,(
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

thf('31',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( X32 = k1_xboole_0 )
      | ( X33 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X32 @ X33 @ X35 @ X34 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k3_zfmisc_1 @ X32 @ X33 @ X35 ) )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('32',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['32','33','34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_E
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['29','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ A ) ) )).

thf('40',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k5_mcart_1 @ X14 @ X15 @ X16 @ X17 ) @ X14 )
      | ~ ( m1_subset_1 @ X17 @ ( k3_zfmisc_1 @ X14 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_mcart_1])).

thf('41',plain,(
    m1_subset_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_A ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( X32 = k1_xboole_0 )
      | ( X33 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X32 @ X33 @ X35 @ X34 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k3_zfmisc_1 @ X32 @ X33 @ X35 ) )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('44',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['44','45','46','47'])).

thf('49',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ),
    inference(demod,[status(thm)],['41','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['38','49'])).

thf('51',plain,
    ( ( sk_E != sk_E )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ) )).

thf('53',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( m1_subset_1 @ ( k7_mcart_1 @ X22 @ X23 @ X24 @ X25 ) @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k3_zfmisc_1 @ X22 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_mcart_1])).

thf('54',plain,(
    m1_subset_1 @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_C ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( X32 = k1_xboole_0 )
      | ( X33 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X32 @ X33 @ X35 @ X34 )
        = ( k2_mcart_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k3_zfmisc_1 @ X32 @ X33 @ X35 ) )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('57',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k2_mcart_1 @ sk_E ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['57','58','59','60'])).

thf('62',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['54','61'])).

thf('63',plain,
    ( ( sk_E != sk_E )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['51','62'])).

thf('64',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_zfmisc_1 @ X11 @ X12 @ X13 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('66',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('67',plain,(
    ! [X1: $i,X2: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X1 )
       != X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X1: $i,X2: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['65','69'])).

thf('71',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','70'])).

thf('72',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X1: $i,X2: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('76',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['77','78','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wYec5xRyo8
% 0.16/0.37  % Computer   : n024.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 15:45:51 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 1.76/1.98  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.76/1.98  % Solved by: fo/fo7.sh
% 1.76/1.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.76/1.98  % done 2339 iterations in 1.496s
% 1.76/1.98  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.76/1.98  % SZS output start Refutation
% 1.76/1.98  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 1.76/1.98  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.76/1.98  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.76/1.98  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 1.76/1.98  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.76/1.98  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 1.76/1.98  thf(sk_E_type, type, sk_E: $i).
% 1.76/1.98  thf(sk_A_type, type, sk_A: $i).
% 1.76/1.98  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 1.76/1.98  thf(sk_D_type, type, sk_D: $i).
% 1.76/1.98  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 1.76/1.98  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.76/1.98  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.76/1.98  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 1.76/1.98  thf(sk_C_type, type, sk_C: $i).
% 1.76/1.98  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.76/1.98  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 1.76/1.98  thf(sk_B_type, type, sk_B: $i).
% 1.76/1.98  thf(t70_mcart_1, conjecture,
% 1.76/1.98    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.76/1.98     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.76/1.98       ( ( ![F:$i]:
% 1.76/1.98           ( ( m1_subset_1 @ F @ A ) =>
% 1.76/1.98             ( ![G:$i]:
% 1.76/1.98               ( ( m1_subset_1 @ G @ B ) =>
% 1.76/1.98                 ( ![H:$i]:
% 1.76/1.98                   ( ( m1_subset_1 @ H @ C ) =>
% 1.76/1.98                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 1.76/1.98                       ( ( D ) = ( G ) ) ) ) ) ) ) ) ) =>
% 1.76/1.98         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.76/1.98           ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.76/1.98           ( ( D ) = ( k6_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 1.76/1.98  thf(zf_stmt_0, negated_conjecture,
% 1.76/1.98    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.76/1.98        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.76/1.98          ( ( ![F:$i]:
% 1.76/1.98              ( ( m1_subset_1 @ F @ A ) =>
% 1.76/1.98                ( ![G:$i]:
% 1.76/1.98                  ( ( m1_subset_1 @ G @ B ) =>
% 1.76/1.98                    ( ![H:$i]:
% 1.76/1.98                      ( ( m1_subset_1 @ H @ C ) =>
% 1.76/1.98                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 1.76/1.98                          ( ( D ) = ( G ) ) ) ) ) ) ) ) ) =>
% 1.76/1.98            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.76/1.98              ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.76/1.98              ( ( D ) = ( k6_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 1.76/1.98    inference('cnf.neg', [status(esa)], [t70_mcart_1])).
% 1.76/1.98  thf('0', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 1.76/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.98  thf(d3_zfmisc_1, axiom,
% 1.76/1.98    (![A:$i,B:$i,C:$i]:
% 1.76/1.98     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 1.76/1.98       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 1.76/1.98  thf('1', plain,
% 1.76/1.98      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.76/1.98         ((k3_zfmisc_1 @ X11 @ X12 @ X13)
% 1.76/1.98           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12) @ X13))),
% 1.76/1.98      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.76/1.98  thf(t24_mcart_1, axiom,
% 1.76/1.98    (![A:$i,B:$i]:
% 1.76/1.98     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.76/1.98          ( ~( ![C:$i]:
% 1.76/1.98               ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 1.76/1.98                 ( ( C ) =
% 1.76/1.98                   ( k4_tarski @ ( k1_mcart_1 @ C ) @ ( k2_mcart_1 @ C ) ) ) ) ) ) ) ))).
% 1.76/1.98  thf('2', plain,
% 1.76/1.98      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.76/1.98         (((X29) = (k1_xboole_0))
% 1.76/1.98          | ((X30) = (k4_tarski @ (k1_mcart_1 @ X30) @ (k2_mcart_1 @ X30)))
% 1.76/1.98          | ~ (m1_subset_1 @ X30 @ (k2_zfmisc_1 @ X29 @ X31))
% 1.76/1.98          | ((X31) = (k1_xboole_0)))),
% 1.76/1.98      inference('cnf', [status(esa)], [t24_mcart_1])).
% 1.76/1.98  thf('3', plain,
% 1.76/1.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.76/1.98         (~ (m1_subset_1 @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.76/1.98          | ((X0) = (k1_xboole_0))
% 1.76/1.98          | ((X3) = (k4_tarski @ (k1_mcart_1 @ X3) @ (k2_mcart_1 @ X3)))
% 1.76/1.98          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0)))),
% 1.76/1.98      inference('sup-', [status(thm)], ['1', '2'])).
% 1.76/1.98  thf('4', plain,
% 1.76/1.98      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 1.76/1.98        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 1.76/1.98        | ((sk_C) = (k1_xboole_0)))),
% 1.76/1.98      inference('sup-', [status(thm)], ['0', '3'])).
% 1.76/1.98  thf('5', plain, (((sk_C) != (k1_xboole_0))),
% 1.76/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.98  thf('6', plain,
% 1.76/1.98      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 1.76/1.98        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 1.76/1.98      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 1.76/1.98  thf('7', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 1.76/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.98  thf(t2_subset, axiom,
% 1.76/1.98    (![A:$i,B:$i]:
% 1.76/1.98     ( ( m1_subset_1 @ A @ B ) =>
% 1.76/1.98       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 1.76/1.98  thf('8', plain,
% 1.76/1.98      (![X6 : $i, X7 : $i]:
% 1.76/1.98         ((r2_hidden @ X6 @ X7)
% 1.76/1.98          | (v1_xboole_0 @ X7)
% 1.76/1.98          | ~ (m1_subset_1 @ X6 @ X7))),
% 1.76/1.98      inference('cnf', [status(esa)], [t2_subset])).
% 1.76/1.98  thf('9', plain,
% 1.76/1.98      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 1.76/1.98        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 1.76/1.98      inference('sup-', [status(thm)], ['7', '8'])).
% 1.76/1.98  thf('10', plain,
% 1.76/1.98      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.76/1.98         ((k3_zfmisc_1 @ X11 @ X12 @ X13)
% 1.76/1.98           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12) @ X13))),
% 1.76/1.98      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.76/1.98  thf(t10_mcart_1, axiom,
% 1.76/1.98    (![A:$i,B:$i,C:$i]:
% 1.76/1.98     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 1.76/1.98       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 1.76/1.98         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 1.76/1.98  thf('11', plain,
% 1.76/1.98      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.76/1.98         ((r2_hidden @ (k1_mcart_1 @ X26) @ X27)
% 1.76/1.98          | ~ (r2_hidden @ X26 @ (k2_zfmisc_1 @ X27 @ X28)))),
% 1.76/1.98      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.76/1.98  thf('12', plain,
% 1.76/1.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.76/1.98         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.76/1.98          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 1.76/1.98      inference('sup-', [status(thm)], ['10', '11'])).
% 1.76/1.98  thf('13', plain,
% 1.76/1.98      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 1.76/1.98        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.76/1.98      inference('sup-', [status(thm)], ['9', '12'])).
% 1.76/1.98  thf(t1_subset, axiom,
% 1.76/1.98    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 1.76/1.98  thf('14', plain,
% 1.76/1.98      (![X4 : $i, X5 : $i]: ((m1_subset_1 @ X4 @ X5) | ~ (r2_hidden @ X4 @ X5))),
% 1.76/1.98      inference('cnf', [status(esa)], [t1_subset])).
% 1.76/1.98  thf('15', plain,
% 1.76/1.98      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 1.76/1.98        | (m1_subset_1 @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.76/1.98      inference('sup-', [status(thm)], ['13', '14'])).
% 1.76/1.98  thf('16', plain,
% 1.76/1.98      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.76/1.98         (((X29) = (k1_xboole_0))
% 1.76/1.98          | ((X30) = (k4_tarski @ (k1_mcart_1 @ X30) @ (k2_mcart_1 @ X30)))
% 1.76/1.98          | ~ (m1_subset_1 @ X30 @ (k2_zfmisc_1 @ X29 @ X31))
% 1.76/1.98          | ((X31) = (k1_xboole_0)))),
% 1.76/1.98      inference('cnf', [status(esa)], [t24_mcart_1])).
% 1.76/1.98  thf('17', plain,
% 1.76/1.98      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 1.76/1.98        | ((sk_B) = (k1_xboole_0))
% 1.76/1.98        | ((k1_mcart_1 @ sk_E)
% 1.76/1.98            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 1.76/1.98               (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 1.76/1.98        | ((sk_A) = (k1_xboole_0)))),
% 1.76/1.98      inference('sup-', [status(thm)], ['15', '16'])).
% 1.76/1.98  thf('18', plain, (((sk_A) != (k1_xboole_0))),
% 1.76/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.98  thf('19', plain, (((sk_B) != (k1_xboole_0))),
% 1.76/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.98  thf('20', plain,
% 1.76/1.98      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 1.76/1.98        | ((k1_mcart_1 @ sk_E)
% 1.76/1.98            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 1.76/1.98               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 1.76/1.98      inference('simplify_reflect-', [status(thm)], ['17', '18', '19'])).
% 1.76/1.98  thf(d3_mcart_1, axiom,
% 1.76/1.98    (![A:$i,B:$i,C:$i]:
% 1.76/1.98     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 1.76/1.98  thf('21', plain,
% 1.76/1.98      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.76/1.98         ((k3_mcart_1 @ X8 @ X9 @ X10)
% 1.76/1.98           = (k4_tarski @ (k4_tarski @ X8 @ X9) @ X10))),
% 1.76/1.98      inference('cnf', [status(esa)], [d3_mcart_1])).
% 1.76/1.98  thf('22', plain,
% 1.76/1.98      (![X0 : $i]:
% 1.76/1.98         (((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 1.76/1.98            (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X0)
% 1.76/1.98            = (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 1.76/1.98          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 1.76/1.98      inference('sup+', [status(thm)], ['20', '21'])).
% 1.76/1.98  thf('23', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 1.76/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.98  thf(dt_k6_mcart_1, axiom,
% 1.76/1.98    (![A:$i,B:$i,C:$i,D:$i]:
% 1.76/1.98     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.76/1.98       ( m1_subset_1 @ ( k6_mcart_1 @ A @ B @ C @ D ) @ B ) ))).
% 1.76/1.98  thf('24', plain,
% 1.76/1.98      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.76/1.98         ((m1_subset_1 @ (k6_mcart_1 @ X18 @ X19 @ X20 @ X21) @ X19)
% 1.76/1.98          | ~ (m1_subset_1 @ X21 @ (k3_zfmisc_1 @ X18 @ X19 @ X20)))),
% 1.76/1.98      inference('cnf', [status(esa)], [dt_k6_mcart_1])).
% 1.76/1.98  thf('25', plain,
% 1.76/1.98      ((m1_subset_1 @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_B)),
% 1.76/1.98      inference('sup-', [status(thm)], ['23', '24'])).
% 1.76/1.98  thf('26', plain,
% 1.76/1.98      (![X36 : $i, X37 : $i, X38 : $i]:
% 1.76/1.98         (~ (m1_subset_1 @ X36 @ sk_B)
% 1.76/1.98          | ((sk_D) = (X36))
% 1.76/1.98          | ((sk_E) != (k3_mcart_1 @ X37 @ X36 @ X38))
% 1.76/1.98          | ~ (m1_subset_1 @ X38 @ sk_C)
% 1.76/1.98          | ~ (m1_subset_1 @ X37 @ sk_A))),
% 1.76/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.98  thf('27', plain,
% 1.76/1.98      (![X0 : $i, X1 : $i]:
% 1.76/1.98         (~ (m1_subset_1 @ X0 @ sk_A)
% 1.76/1.98          | ~ (m1_subset_1 @ X1 @ sk_C)
% 1.76/1.98          | ((sk_E)
% 1.76/1.98              != (k3_mcart_1 @ X0 @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.76/1.98                  X1))
% 1.76/1.98          | ((sk_D) = (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)))),
% 1.76/1.98      inference('sup-', [status(thm)], ['25', '26'])).
% 1.76/1.98  thf('28', plain, (((sk_D) != (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E))),
% 1.76/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.98  thf('29', plain,
% 1.76/1.98      (![X0 : $i, X1 : $i]:
% 1.76/1.98         (~ (m1_subset_1 @ X0 @ sk_A)
% 1.76/1.98          | ~ (m1_subset_1 @ X1 @ sk_C)
% 1.76/1.98          | ((sk_E)
% 1.76/1.98              != (k3_mcart_1 @ X0 @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 1.76/1.98                  X1)))),
% 1.76/1.98      inference('simplify_reflect-', [status(thm)], ['27', '28'])).
% 1.76/1.98  thf('30', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 1.76/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.98  thf(t50_mcart_1, axiom,
% 1.76/1.98    (![A:$i,B:$i,C:$i]:
% 1.76/1.98     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.76/1.98          ( ( C ) != ( k1_xboole_0 ) ) & 
% 1.76/1.98          ( ~( ![D:$i]:
% 1.76/1.98               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.76/1.98                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 1.76/1.98                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 1.76/1.98                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 1.76/1.98                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 1.76/1.98                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 1.76/1.98  thf('31', plain,
% 1.76/1.98      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.76/1.98         (((X32) = (k1_xboole_0))
% 1.76/1.98          | ((X33) = (k1_xboole_0))
% 1.76/1.98          | ((k6_mcart_1 @ X32 @ X33 @ X35 @ X34)
% 1.76/1.98              = (k2_mcart_1 @ (k1_mcart_1 @ X34)))
% 1.76/1.98          | ~ (m1_subset_1 @ X34 @ (k3_zfmisc_1 @ X32 @ X33 @ X35))
% 1.76/1.98          | ((X35) = (k1_xboole_0)))),
% 1.76/1.98      inference('cnf', [status(esa)], [t50_mcart_1])).
% 1.76/1.98  thf('32', plain,
% 1.76/1.98      ((((sk_C) = (k1_xboole_0))
% 1.76/1.98        | ((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 1.76/1.98            = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 1.76/1.98        | ((sk_B) = (k1_xboole_0))
% 1.76/1.98        | ((sk_A) = (k1_xboole_0)))),
% 1.76/1.98      inference('sup-', [status(thm)], ['30', '31'])).
% 1.76/1.98  thf('33', plain, (((sk_A) != (k1_xboole_0))),
% 1.76/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.98  thf('34', plain, (((sk_B) != (k1_xboole_0))),
% 1.76/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.98  thf('35', plain, (((sk_C) != (k1_xboole_0))),
% 1.76/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.98  thf('36', plain,
% 1.76/1.98      (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 1.76/1.98         = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 1.76/1.98      inference('simplify_reflect-', [status(thm)], ['32', '33', '34', '35'])).
% 1.76/1.98  thf('37', plain,
% 1.76/1.98      (![X0 : $i, X1 : $i]:
% 1.76/1.98         (~ (m1_subset_1 @ X0 @ sk_A)
% 1.76/1.98          | ~ (m1_subset_1 @ X1 @ sk_C)
% 1.76/1.98          | ((sk_E)
% 1.76/1.98              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1)))),
% 1.76/1.98      inference('demod', [status(thm)], ['29', '36'])).
% 1.76/1.98  thf('38', plain,
% 1.76/1.98      (![X0 : $i]:
% 1.76/1.98         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 1.76/1.98          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 1.76/1.98          | ~ (m1_subset_1 @ X0 @ sk_C)
% 1.76/1.98          | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 1.76/1.98      inference('sup-', [status(thm)], ['22', '37'])).
% 1.76/1.98  thf('39', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 1.76/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.98  thf(dt_k5_mcart_1, axiom,
% 1.76/1.98    (![A:$i,B:$i,C:$i,D:$i]:
% 1.76/1.98     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.76/1.98       ( m1_subset_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ A ) ))).
% 1.76/1.98  thf('40', plain,
% 1.76/1.98      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 1.76/1.98         ((m1_subset_1 @ (k5_mcart_1 @ X14 @ X15 @ X16 @ X17) @ X14)
% 1.76/1.98          | ~ (m1_subset_1 @ X17 @ (k3_zfmisc_1 @ X14 @ X15 @ X16)))),
% 1.76/1.98      inference('cnf', [status(esa)], [dt_k5_mcart_1])).
% 1.76/1.98  thf('41', plain,
% 1.76/1.98      ((m1_subset_1 @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_A)),
% 1.76/1.98      inference('sup-', [status(thm)], ['39', '40'])).
% 1.76/1.98  thf('42', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 1.76/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.98  thf('43', plain,
% 1.76/1.98      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.76/1.98         (((X32) = (k1_xboole_0))
% 1.76/1.98          | ((X33) = (k1_xboole_0))
% 1.76/1.98          | ((k5_mcart_1 @ X32 @ X33 @ X35 @ X34)
% 1.76/1.98              = (k1_mcart_1 @ (k1_mcart_1 @ X34)))
% 1.76/1.98          | ~ (m1_subset_1 @ X34 @ (k3_zfmisc_1 @ X32 @ X33 @ X35))
% 1.76/1.98          | ((X35) = (k1_xboole_0)))),
% 1.76/1.98      inference('cnf', [status(esa)], [t50_mcart_1])).
% 1.76/1.98  thf('44', plain,
% 1.76/1.98      ((((sk_C) = (k1_xboole_0))
% 1.76/1.98        | ((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 1.76/1.98            = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 1.76/1.98        | ((sk_B) = (k1_xboole_0))
% 1.76/1.98        | ((sk_A) = (k1_xboole_0)))),
% 1.76/1.98      inference('sup-', [status(thm)], ['42', '43'])).
% 1.76/1.98  thf('45', plain, (((sk_A) != (k1_xboole_0))),
% 1.76/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.98  thf('46', plain, (((sk_B) != (k1_xboole_0))),
% 1.76/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.98  thf('47', plain, (((sk_C) != (k1_xboole_0))),
% 1.76/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.98  thf('48', plain,
% 1.76/1.98      (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 1.76/1.98         = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 1.76/1.98      inference('simplify_reflect-', [status(thm)], ['44', '45', '46', '47'])).
% 1.76/1.98  thf('49', plain, ((m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)),
% 1.76/1.98      inference('demod', [status(thm)], ['41', '48'])).
% 1.76/1.98  thf('50', plain,
% 1.76/1.98      (![X0 : $i]:
% 1.76/1.98         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 1.76/1.98          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 1.76/1.98          | ~ (m1_subset_1 @ X0 @ sk_C))),
% 1.76/1.98      inference('demod', [status(thm)], ['38', '49'])).
% 1.76/1.98  thf('51', plain,
% 1.76/1.98      ((((sk_E) != (sk_E))
% 1.76/1.98        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 1.76/1.98        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)
% 1.76/1.98        | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 1.76/1.98      inference('sup-', [status(thm)], ['6', '50'])).
% 1.76/1.98  thf('52', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 1.76/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.98  thf(dt_k7_mcart_1, axiom,
% 1.76/1.98    (![A:$i,B:$i,C:$i,D:$i]:
% 1.76/1.98     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.76/1.98       ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ))).
% 1.76/1.98  thf('53', plain,
% 1.76/1.98      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 1.76/1.98         ((m1_subset_1 @ (k7_mcart_1 @ X22 @ X23 @ X24 @ X25) @ X24)
% 1.76/1.98          | ~ (m1_subset_1 @ X25 @ (k3_zfmisc_1 @ X22 @ X23 @ X24)))),
% 1.76/1.98      inference('cnf', [status(esa)], [dt_k7_mcart_1])).
% 1.76/1.98  thf('54', plain,
% 1.76/1.98      ((m1_subset_1 @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_C)),
% 1.76/1.98      inference('sup-', [status(thm)], ['52', '53'])).
% 1.76/1.98  thf('55', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 1.76/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.98  thf('56', plain,
% 1.76/1.98      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.76/1.98         (((X32) = (k1_xboole_0))
% 1.76/1.98          | ((X33) = (k1_xboole_0))
% 1.76/1.98          | ((k7_mcart_1 @ X32 @ X33 @ X35 @ X34) = (k2_mcart_1 @ X34))
% 1.76/1.98          | ~ (m1_subset_1 @ X34 @ (k3_zfmisc_1 @ X32 @ X33 @ X35))
% 1.76/1.98          | ((X35) = (k1_xboole_0)))),
% 1.76/1.98      inference('cnf', [status(esa)], [t50_mcart_1])).
% 1.76/1.98  thf('57', plain,
% 1.76/1.98      ((((sk_C) = (k1_xboole_0))
% 1.76/1.98        | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))
% 1.76/1.98        | ((sk_B) = (k1_xboole_0))
% 1.76/1.98        | ((sk_A) = (k1_xboole_0)))),
% 1.76/1.98      inference('sup-', [status(thm)], ['55', '56'])).
% 1.76/1.98  thf('58', plain, (((sk_A) != (k1_xboole_0))),
% 1.76/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.98  thf('59', plain, (((sk_B) != (k1_xboole_0))),
% 1.76/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.98  thf('60', plain, (((sk_C) != (k1_xboole_0))),
% 1.76/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.98  thf('61', plain,
% 1.76/1.98      (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))),
% 1.76/1.98      inference('simplify_reflect-', [status(thm)], ['57', '58', '59', '60'])).
% 1.76/1.98  thf('62', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)),
% 1.76/1.98      inference('demod', [status(thm)], ['54', '61'])).
% 1.76/1.98  thf('63', plain,
% 1.76/1.98      ((((sk_E) != (sk_E))
% 1.76/1.98        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 1.76/1.98        | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 1.76/1.98      inference('demod', [status(thm)], ['51', '62'])).
% 1.76/1.98  thf('64', plain,
% 1.76/1.98      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 1.76/1.98        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 1.76/1.98      inference('simplify', [status(thm)], ['63'])).
% 1.76/1.98  thf('65', plain,
% 1.76/1.98      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.76/1.98         ((k3_zfmisc_1 @ X11 @ X12 @ X13)
% 1.76/1.98           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12) @ X13))),
% 1.76/1.98      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.76/1.98  thf(l13_xboole_0, axiom,
% 1.76/1.98    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.76/1.98  thf('66', plain,
% 1.76/1.98      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.76/1.98      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.76/1.98  thf(t113_zfmisc_1, axiom,
% 1.76/1.98    (![A:$i,B:$i]:
% 1.76/1.98     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.76/1.98       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.76/1.98  thf('67', plain,
% 1.76/1.98      (![X1 : $i, X2 : $i]:
% 1.76/1.98         (((X1) = (k1_xboole_0))
% 1.76/1.98          | ((X2) = (k1_xboole_0))
% 1.76/1.98          | ((k2_zfmisc_1 @ X2 @ X1) != (k1_xboole_0)))),
% 1.76/1.98      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.76/1.98  thf('68', plain,
% 1.76/1.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.76/1.98         (((k2_zfmisc_1 @ X2 @ X1) != (X0))
% 1.76/1.98          | ~ (v1_xboole_0 @ X0)
% 1.76/1.98          | ((X2) = (k1_xboole_0))
% 1.76/1.98          | ((X1) = (k1_xboole_0)))),
% 1.76/1.98      inference('sup-', [status(thm)], ['66', '67'])).
% 1.76/1.98  thf('69', plain,
% 1.76/1.98      (![X1 : $i, X2 : $i]:
% 1.76/1.98         (((X1) = (k1_xboole_0))
% 1.76/1.98          | ((X2) = (k1_xboole_0))
% 1.76/1.98          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1)))),
% 1.76/1.98      inference('simplify', [status(thm)], ['68'])).
% 1.76/1.98  thf('70', plain,
% 1.76/1.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.76/1.98         (~ (v1_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.76/1.98          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 1.76/1.98          | ((X0) = (k1_xboole_0)))),
% 1.76/1.98      inference('sup-', [status(thm)], ['65', '69'])).
% 1.76/1.98  thf('71', plain,
% 1.76/1.98      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 1.76/1.98        | ((sk_C) = (k1_xboole_0))
% 1.76/1.98        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 1.76/1.98      inference('sup-', [status(thm)], ['64', '70'])).
% 1.76/1.98  thf('72', plain,
% 1.76/1.98      ((((sk_C) = (k1_xboole_0))
% 1.76/1.98        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 1.76/1.98      inference('simplify', [status(thm)], ['71'])).
% 1.76/1.98  thf('73', plain, (((sk_C) != (k1_xboole_0))),
% 1.76/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.98  thf('74', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 1.76/1.98      inference('simplify_reflect-', [status(thm)], ['72', '73'])).
% 1.76/1.98  thf('75', plain,
% 1.76/1.98      (![X1 : $i, X2 : $i]:
% 1.76/1.98         (((X1) = (k1_xboole_0))
% 1.76/1.98          | ((X2) = (k1_xboole_0))
% 1.76/1.98          | ((k2_zfmisc_1 @ X2 @ X1) != (k1_xboole_0)))),
% 1.76/1.98      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.76/1.98  thf('76', plain,
% 1.76/1.98      ((((k1_xboole_0) != (k1_xboole_0))
% 1.76/1.98        | ((sk_A) = (k1_xboole_0))
% 1.76/1.98        | ((sk_B) = (k1_xboole_0)))),
% 1.76/1.98      inference('sup-', [status(thm)], ['74', '75'])).
% 1.76/1.98  thf('77', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 1.76/1.98      inference('simplify', [status(thm)], ['76'])).
% 1.76/1.98  thf('78', plain, (((sk_A) != (k1_xboole_0))),
% 1.76/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.98  thf('79', plain, (((sk_B) != (k1_xboole_0))),
% 1.76/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/1.98  thf('80', plain, ($false),
% 1.76/1.98      inference('simplify_reflect-', [status(thm)], ['77', '78', '79'])).
% 1.76/1.98  
% 1.76/1.98  % SZS output end Refutation
% 1.76/1.98  
% 1.77/1.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
