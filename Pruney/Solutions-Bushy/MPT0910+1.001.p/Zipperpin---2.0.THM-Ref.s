%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0910+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2KnUH0K3zR

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:42 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   41 (  57 expanded)
%              Number of leaves         :   17 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :  408 (1048 expanded)
%              Number of equality atoms :   36 ( 132 expanded)
%              Maximal formula depth    :   20 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

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
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ( X15
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X12 @ X13 @ X14 @ X15 ) @ ( k6_mcart_1 @ X12 @ X13 @ X14 @ X15 ) @ ( k7_mcart_1 @ X12 @ X13 @ X14 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k3_zfmisc_1 @ X12 @ X13 @ X14 ) )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t48_mcart_1])).

thf('2',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_E
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( sk_E
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k6_mcart_1 @ A @ B @ C @ D ) @ B ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k6_mcart_1 @ X4 @ X5 @ X6 @ X7 ) @ X5 )
      | ~ ( m1_subset_1 @ X7 @ ( k3_zfmisc_1 @ X4 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_mcart_1])).

thf('9',plain,(
    m1_subset_1 @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ sk_B )
      | ( sk_D = X16 )
      | ( sk_E
       != ( k3_mcart_1 @ X17 @ X16 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ sk_C )
      | ~ ( m1_subset_1 @ X17 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_E
       != ( k3_mcart_1 @ X0 @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ X1 ) )
      | ( sk_D
        = ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    sk_D
 != ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_E
       != ( k3_mcart_1 @ X0 @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ X1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_E != sk_E )
    | ~ ( m1_subset_1 @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_C )
    | ~ ( m1_subset_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_A ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ) )).

thf('16',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( m1_subset_1 @ ( k7_mcart_1 @ X8 @ X9 @ X10 @ X11 ) @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k3_zfmisc_1 @ X8 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_mcart_1])).

thf('17',plain,(
    m1_subset_1 @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_C ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ A ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( m1_subset_1 @ ( k5_mcart_1 @ X0 @ X1 @ X2 @ X3 ) @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( k3_zfmisc_1 @ X0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_mcart_1])).

thf('20',plain,(
    m1_subset_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_A ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    sk_E != sk_E ),
    inference(demod,[status(thm)],['14','17','20'])).

thf('22',plain,(
    $false ),
    inference(simplify,[status(thm)],['21'])).


%------------------------------------------------------------------------------
