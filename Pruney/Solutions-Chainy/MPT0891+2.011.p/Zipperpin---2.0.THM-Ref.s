%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zvhirTIacA

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:34 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 494 expanded)
%              Number of leaves         :   34 ( 164 expanded)
%              Depth                    :   14
%              Number of atoms          : 1290 (8584 expanded)
%              Number of equality atoms :  187 (1329 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t51_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( ( D
                 != ( k5_mcart_1 @ A @ B @ C @ D ) )
                & ( D
                 != ( k6_mcart_1 @ A @ B @ C @ D ) )
                & ( D
                 != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 )
          & ~ ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
               => ( ( D
                   != ( k5_mcart_1 @ A @ B @ C @ D ) )
                  & ( D
                   != ( k6_mcart_1 @ A @ B @ C @ D ) )
                  & ( D
                   != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t51_mcart_1])).

thf('0',plain,(
    m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('1',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( k3_zfmisc_1 @ X30 @ X31 @ X32 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t48_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( D
                = ( k3_mcart_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ ( k6_mcart_1 @ A @ B @ C @ D ) @ ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf('3',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( X40 = k1_xboole_0 )
      | ( X41 = k1_xboole_0 )
      | ( X43
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X40 @ X41 @ X42 @ X43 ) @ ( k6_mcart_1 @ X40 @ X41 @ X42 @ X43 ) @ ( k7_mcart_1 @ X40 @ X41 @ X42 @ X43 ) ) )
      | ~ ( m1_subset_1 @ X43 @ ( k3_zfmisc_1 @ X40 @ X41 @ X42 ) )
      | ( X42 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t48_mcart_1])).

thf('4',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( k3_zfmisc_1 @ X30 @ X31 @ X32 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('5',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( X40 = k1_xboole_0 )
      | ( X41 = k1_xboole_0 )
      | ( X43
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X40 @ X41 @ X42 @ X43 ) @ ( k6_mcart_1 @ X40 @ X41 @ X42 @ X43 ) @ ( k7_mcart_1 @ X40 @ X41 @ X42 @ X43 ) ) )
      | ~ ( m1_subset_1 @ X43 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) @ X42 ) )
      | ( X42 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_D
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

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
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( X44 = k1_xboole_0 )
      | ( X45 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X44 @ X45 @ X47 @ X46 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X46 ) ) )
      | ~ ( m1_subset_1 @ X46 @ ( k3_zfmisc_1 @ X44 @ X45 @ X47 ) )
      | ( X47 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('9',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( k3_zfmisc_1 @ X30 @ X31 @ X32 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('10',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( X44 = k1_xboole_0 )
      | ( X45 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X44 @ X45 @ X47 @ X46 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X46 ) ) )
      | ~ ( m1_subset_1 @ X46 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) @ X47 ) )
      | ( X47 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['11','12','13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('17',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( X44 = k1_xboole_0 )
      | ( X45 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X44 @ X45 @ X47 @ X46 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X46 ) ) )
      | ~ ( m1_subset_1 @ X46 @ ( k3_zfmisc_1 @ X44 @ X45 @ X47 ) )
      | ( X47 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('18',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( k3_zfmisc_1 @ X30 @ X31 @ X32 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('19',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( X44 = k1_xboole_0 )
      | ( X45 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X44 @ X45 @ X47 @ X46 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X46 ) ) )
      | ~ ( m1_subset_1 @ X46 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) @ X47 ) )
      | ( X47 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['20','21','22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('26',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( X44 = k1_xboole_0 )
      | ( X45 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X44 @ X45 @ X47 @ X46 )
        = ( k2_mcart_1 @ X46 ) )
      | ~ ( m1_subset_1 @ X46 @ ( k3_zfmisc_1 @ X44 @ X45 @ X47 ) )
      | ( X47 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('27',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( k3_zfmisc_1 @ X30 @ X31 @ X32 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('28',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( X44 = k1_xboole_0 )
      | ( X45 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X44 @ X45 @ X47 @ X46 )
        = ( k2_mcart_1 @ X46 ) )
      | ~ ( m1_subset_1 @ X46 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) @ X47 ) )
      | ( X47 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D )
      = ( k2_mcart_1 @ sk_D ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D )
    = ( k2_mcart_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['29','30','31','32'])).

thf('34',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_D
      = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ sk_D ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','15','24','33'])).

thf('35',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['34','35','36','37'])).

thf(t29_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) )).

thf('39',plain,(
    ! [X36: $i] :
      ( ( X36 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X36 ) @ X36 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('40',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X18 ) @ ( k1_tarski @ X19 ) )
        = ( k1_tarski @ X18 ) )
      | ( X18 = X19 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('41',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ( ( k4_xboole_0 @ X21 @ ( k1_tarski @ X20 ) )
       != X21 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( X0 = X1 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( sk_B @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['39','43'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('45',plain,(
    ! [X14: $i] :
      ( ( k2_tarski @ X14 @ X14 )
      = ( k1_tarski @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t73_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = k1_xboole_0 )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('47',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ X23 @ X24 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X23 @ X25 ) @ X24 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t73_zfmisc_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_tarski @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('49',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('50',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ( ( k4_xboole_0 @ X21 @ ( k1_tarski @ X20 ) )
       != X21 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['48','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( X0
      = ( sk_B @ ( k1_tarski @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['44','54'])).

thf('56',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( X36 = k1_xboole_0 )
      | ~ ( r2_hidden @ X37 @ X36 )
      | ( ( sk_B @ X36 )
       != ( k3_mcart_1 @ X38 @ X37 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0
       != ( k3_mcart_1 @ X3 @ X2 @ X1 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','53'])).

thf('60',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ~ ( r2_hidden @ X2 @ ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k1_tarski @ sk_D ) ) ),
    inference('sup-',[status(thm)],['38','60'])).

thf('62',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['20','21','22','23'])).

thf('63',plain,
    ( ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) )
    | ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) )
    | ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) )
   <= ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['63'])).

thf('65',plain,
    ( ( sk_D
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) )
   <= ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('sup+',[status(thm)],['62','64'])).

thf('66',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D )
    = ( k2_mcart_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['29','30','31','32'])).

thf('67',plain,
    ( ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) )
   <= ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['63'])).

thf('68',plain,
    ( ( sk_D
      = ( k2_mcart_1 @ sk_D ) )
   <= ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['34','35','36','37'])).

thf('70',plain,
    ( ( sk_D
      = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ sk_D ) )
   <= ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('71',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k3_mcart_1 @ X27 @ X28 @ X29 )
      = ( k4_tarski @ ( k4_tarski @ X27 @ X28 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(t20_mcart_1,axiom,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf('72',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X33
       != ( k2_mcart_1 @ X33 ) )
      | ( X33
       != ( k4_tarski @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('73',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k4_tarski @ X34 @ X35 )
     != ( k2_mcart_1 @ ( k4_tarski @ X34 @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('74',plain,(
    ! [X48: $i,X50: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X48 @ X50 ) )
      = X50 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('75',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k4_tarski @ X34 @ X35 )
     != X35 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X2 @ X1 @ X0 )
     != X0 ) ),
    inference('sup-',[status(thm)],['71','75'])).

thf('77',plain,(
    sk_D
 != ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['70','76'])).

thf('78',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['11','12','13','14'])).

thf('79',plain,
    ( ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['63'])).

thf('80',plain,
    ( ( sk_D
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['34','35','36','37'])).

thf('82',plain,
    ( ( sk_D
      = ( k3_mcart_1 @ sk_D @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) @ ( k2_mcart_1 @ sk_D ) ) )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( X0
      = ( sk_B @ ( k1_tarski @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['44','54'])).

thf('84',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( X36 = k1_xboole_0 )
      | ~ ( r2_hidden @ X38 @ X36 )
      | ( ( sk_B @ X36 )
       != ( k3_mcart_1 @ X38 @ X37 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0
       != ( k3_mcart_1 @ X3 @ X2 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','53'])).

thf('88',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ~ ( r2_hidden @ X3 @ ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( r2_hidden @ sk_D @ ( k1_tarski @ sk_D ) )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['82','88'])).

thf('90',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_xboole_0 @ X21 @ ( k1_tarski @ X22 ) )
        = X21 )
      | ( r2_hidden @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('91',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X18 != X17 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X18 ) @ ( k1_tarski @ X17 ) )
       != ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('92',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X17 ) @ ( k1_tarski @ X17 ) )
     != ( k1_tarski @ X17 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['90','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    sk_D
 != ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['89','94'])).

thf('96',plain,
    ( ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) )
    | ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) )
    | ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['63'])).

thf('97',plain,
    ( sk_D
    = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['77','95','96'])).

thf('98',plain,
    ( sk_D
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D ) ) ),
    inference(simpl_trail,[status(thm)],['65','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('100',plain,(
    $false ),
    inference(demod,[status(thm)],['61','98','99'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zvhirTIacA
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:52:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 98 iterations in 0.038s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.48  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.48  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.19/0.48  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.19/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.48  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.19/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.48  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.19/0.48  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.19/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.48  thf(t51_mcart_1, conjecture,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.48          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.19/0.48          ( ~( ![D:$i]:
% 0.19/0.48               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.19/0.48                 ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.19/0.48                   ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.19/0.48                   ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.48        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.48             ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.19/0.48             ( ~( ![D:$i]:
% 0.19/0.48                  ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.19/0.48                    ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.19/0.48                      ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.19/0.48                      ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t51_mcart_1])).
% 0.19/0.48  thf('0', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_D @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(d3_zfmisc_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.19/0.48       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.19/0.48  thf('1', plain,
% 0.19/0.48      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.19/0.48         ((k3_zfmisc_1 @ X30 @ X31 @ X32)
% 0.19/0.48           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31) @ X32))),
% 0.19/0.48      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.19/0.48  thf('2', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_D @ 
% 0.19/0.48        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C))),
% 0.19/0.48      inference('demod', [status(thm)], ['0', '1'])).
% 0.19/0.48  thf(t48_mcart_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.48          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.19/0.48          ( ~( ![D:$i]:
% 0.19/0.48               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.19/0.48                 ( ( D ) =
% 0.19/0.48                   ( k3_mcart_1 @
% 0.19/0.48                     ( k5_mcart_1 @ A @ B @ C @ D ) @ 
% 0.19/0.48                     ( k6_mcart_1 @ A @ B @ C @ D ) @ 
% 0.19/0.48                     ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.19/0.48         (((X40) = (k1_xboole_0))
% 0.19/0.48          | ((X41) = (k1_xboole_0))
% 0.19/0.48          | ((X43)
% 0.19/0.48              = (k3_mcart_1 @ (k5_mcart_1 @ X40 @ X41 @ X42 @ X43) @ 
% 0.19/0.48                 (k6_mcart_1 @ X40 @ X41 @ X42 @ X43) @ 
% 0.19/0.48                 (k7_mcart_1 @ X40 @ X41 @ X42 @ X43)))
% 0.19/0.48          | ~ (m1_subset_1 @ X43 @ (k3_zfmisc_1 @ X40 @ X41 @ X42))
% 0.19/0.48          | ((X42) = (k1_xboole_0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t48_mcart_1])).
% 0.19/0.48  thf('4', plain,
% 0.19/0.48      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.19/0.48         ((k3_zfmisc_1 @ X30 @ X31 @ X32)
% 0.19/0.48           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31) @ X32))),
% 0.19/0.48      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.19/0.48  thf('5', plain,
% 0.19/0.48      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.19/0.48         (((X40) = (k1_xboole_0))
% 0.19/0.48          | ((X41) = (k1_xboole_0))
% 0.19/0.48          | ((X43)
% 0.19/0.48              = (k3_mcart_1 @ (k5_mcart_1 @ X40 @ X41 @ X42 @ X43) @ 
% 0.19/0.48                 (k6_mcart_1 @ X40 @ X41 @ X42 @ X43) @ 
% 0.19/0.48                 (k7_mcart_1 @ X40 @ X41 @ X42 @ X43)))
% 0.19/0.48          | ~ (m1_subset_1 @ X43 @ 
% 0.19/0.48               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41) @ X42))
% 0.19/0.48          | ((X42) = (k1_xboole_0)))),
% 0.19/0.48      inference('demod', [status(thm)], ['3', '4'])).
% 0.19/0.48  thf('6', plain,
% 0.19/0.48      ((((sk_C) = (k1_xboole_0))
% 0.19/0.48        | ((sk_D)
% 0.19/0.48            = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ 
% 0.19/0.48               (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ 
% 0.19/0.48               (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)))
% 0.19/0.48        | ((sk_B_1) = (k1_xboole_0))
% 0.19/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['2', '5'])).
% 0.19/0.48  thf('7', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_D @ 
% 0.19/0.48        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C))),
% 0.19/0.48      inference('demod', [status(thm)], ['0', '1'])).
% 0.19/0.48  thf(t50_mcart_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.48          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.19/0.48          ( ~( ![D:$i]:
% 0.19/0.48               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.19/0.48                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.19/0.48                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.19/0.48                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.19/0.48                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.19/0.48                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.19/0.48  thf('8', plain,
% 0.19/0.48      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.19/0.48         (((X44) = (k1_xboole_0))
% 0.19/0.48          | ((X45) = (k1_xboole_0))
% 0.19/0.48          | ((k5_mcart_1 @ X44 @ X45 @ X47 @ X46)
% 0.19/0.48              = (k1_mcart_1 @ (k1_mcart_1 @ X46)))
% 0.19/0.48          | ~ (m1_subset_1 @ X46 @ (k3_zfmisc_1 @ X44 @ X45 @ X47))
% 0.19/0.48          | ((X47) = (k1_xboole_0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.19/0.48  thf('9', plain,
% 0.19/0.48      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.19/0.48         ((k3_zfmisc_1 @ X30 @ X31 @ X32)
% 0.19/0.48           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31) @ X32))),
% 0.19/0.48      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.19/0.48  thf('10', plain,
% 0.19/0.48      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.19/0.48         (((X44) = (k1_xboole_0))
% 0.19/0.48          | ((X45) = (k1_xboole_0))
% 0.19/0.48          | ((k5_mcart_1 @ X44 @ X45 @ X47 @ X46)
% 0.19/0.48              = (k1_mcart_1 @ (k1_mcart_1 @ X46)))
% 0.19/0.48          | ~ (m1_subset_1 @ X46 @ 
% 0.19/0.48               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45) @ X47))
% 0.19/0.48          | ((X47) = (k1_xboole_0)))),
% 0.19/0.48      inference('demod', [status(thm)], ['8', '9'])).
% 0.19/0.48  thf('11', plain,
% 0.19/0.48      ((((sk_C) = (k1_xboole_0))
% 0.19/0.48        | ((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)
% 0.19/0.48            = (k1_mcart_1 @ (k1_mcart_1 @ sk_D)))
% 0.19/0.48        | ((sk_B_1) = (k1_xboole_0))
% 0.19/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['7', '10'])).
% 0.19/0.48  thf('12', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('13', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('14', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('15', plain,
% 0.19/0.48      (((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)
% 0.19/0.48         = (k1_mcart_1 @ (k1_mcart_1 @ sk_D)))),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['11', '12', '13', '14'])).
% 0.19/0.48  thf('16', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_D @ 
% 0.19/0.48        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C))),
% 0.19/0.48      inference('demod', [status(thm)], ['0', '1'])).
% 0.19/0.48  thf('17', plain,
% 0.19/0.48      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.19/0.48         (((X44) = (k1_xboole_0))
% 0.19/0.48          | ((X45) = (k1_xboole_0))
% 0.19/0.48          | ((k6_mcart_1 @ X44 @ X45 @ X47 @ X46)
% 0.19/0.48              = (k2_mcart_1 @ (k1_mcart_1 @ X46)))
% 0.19/0.48          | ~ (m1_subset_1 @ X46 @ (k3_zfmisc_1 @ X44 @ X45 @ X47))
% 0.19/0.48          | ((X47) = (k1_xboole_0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.19/0.48  thf('18', plain,
% 0.19/0.48      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.19/0.48         ((k3_zfmisc_1 @ X30 @ X31 @ X32)
% 0.19/0.48           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31) @ X32))),
% 0.19/0.48      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.19/0.48  thf('19', plain,
% 0.19/0.48      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.19/0.48         (((X44) = (k1_xboole_0))
% 0.19/0.48          | ((X45) = (k1_xboole_0))
% 0.19/0.48          | ((k6_mcart_1 @ X44 @ X45 @ X47 @ X46)
% 0.19/0.48              = (k2_mcart_1 @ (k1_mcart_1 @ X46)))
% 0.19/0.48          | ~ (m1_subset_1 @ X46 @ 
% 0.19/0.48               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45) @ X47))
% 0.19/0.48          | ((X47) = (k1_xboole_0)))),
% 0.19/0.48      inference('demod', [status(thm)], ['17', '18'])).
% 0.19/0.48  thf('20', plain,
% 0.19/0.48      ((((sk_C) = (k1_xboole_0))
% 0.19/0.48        | ((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)
% 0.19/0.48            = (k2_mcart_1 @ (k1_mcart_1 @ sk_D)))
% 0.19/0.48        | ((sk_B_1) = (k1_xboole_0))
% 0.19/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['16', '19'])).
% 0.19/0.48  thf('21', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('22', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('23', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('24', plain,
% 0.19/0.48      (((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)
% 0.19/0.48         = (k2_mcart_1 @ (k1_mcart_1 @ sk_D)))),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['20', '21', '22', '23'])).
% 0.19/0.48  thf('25', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_D @ 
% 0.19/0.48        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C))),
% 0.19/0.48      inference('demod', [status(thm)], ['0', '1'])).
% 0.19/0.48  thf('26', plain,
% 0.19/0.48      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.19/0.48         (((X44) = (k1_xboole_0))
% 0.19/0.48          | ((X45) = (k1_xboole_0))
% 0.19/0.48          | ((k7_mcart_1 @ X44 @ X45 @ X47 @ X46) = (k2_mcart_1 @ X46))
% 0.19/0.48          | ~ (m1_subset_1 @ X46 @ (k3_zfmisc_1 @ X44 @ X45 @ X47))
% 0.19/0.48          | ((X47) = (k1_xboole_0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.19/0.48  thf('27', plain,
% 0.19/0.48      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.19/0.48         ((k3_zfmisc_1 @ X30 @ X31 @ X32)
% 0.19/0.48           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31) @ X32))),
% 0.19/0.48      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.19/0.48  thf('28', plain,
% 0.19/0.48      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.19/0.48         (((X44) = (k1_xboole_0))
% 0.19/0.48          | ((X45) = (k1_xboole_0))
% 0.19/0.48          | ((k7_mcart_1 @ X44 @ X45 @ X47 @ X46) = (k2_mcart_1 @ X46))
% 0.19/0.48          | ~ (m1_subset_1 @ X46 @ 
% 0.19/0.48               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45) @ X47))
% 0.19/0.48          | ((X47) = (k1_xboole_0)))),
% 0.19/0.48      inference('demod', [status(thm)], ['26', '27'])).
% 0.19/0.48  thf('29', plain,
% 0.19/0.48      ((((sk_C) = (k1_xboole_0))
% 0.19/0.48        | ((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) = (k2_mcart_1 @ sk_D))
% 0.19/0.48        | ((sk_B_1) = (k1_xboole_0))
% 0.19/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['25', '28'])).
% 0.19/0.48  thf('30', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('31', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('32', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('33', plain,
% 0.19/0.48      (((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) = (k2_mcart_1 @ sk_D))),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['29', '30', '31', '32'])).
% 0.19/0.48  thf('34', plain,
% 0.19/0.48      ((((sk_C) = (k1_xboole_0))
% 0.19/0.48        | ((sk_D)
% 0.19/0.48            = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D)) @ 
% 0.19/0.48               (k2_mcart_1 @ (k1_mcart_1 @ sk_D)) @ (k2_mcart_1 @ sk_D)))
% 0.19/0.48        | ((sk_B_1) = (k1_xboole_0))
% 0.19/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.48      inference('demod', [status(thm)], ['6', '15', '24', '33'])).
% 0.19/0.48  thf('35', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('36', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('37', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('38', plain,
% 0.19/0.48      (((sk_D)
% 0.19/0.48         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D)) @ 
% 0.19/0.48            (k2_mcart_1 @ (k1_mcart_1 @ sk_D)) @ (k2_mcart_1 @ sk_D)))),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['34', '35', '36', '37'])).
% 0.19/0.48  thf(t29_mcart_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.19/0.48          ( ![B:$i]:
% 0.19/0.48            ( ~( ( r2_hidden @ B @ A ) & 
% 0.19/0.48                 ( ![C:$i,D:$i,E:$i]:
% 0.19/0.48                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.19/0.48                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.48  thf('39', plain,
% 0.19/0.48      (![X36 : $i]:
% 0.19/0.48         (((X36) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X36) @ X36))),
% 0.19/0.48      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.19/0.48  thf(t20_zfmisc_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.19/0.48         ( k1_tarski @ A ) ) <=>
% 0.19/0.48       ( ( A ) != ( B ) ) ))).
% 0.19/0.48  thf('40', plain,
% 0.19/0.48      (![X18 : $i, X19 : $i]:
% 0.19/0.48         (((k4_xboole_0 @ (k1_tarski @ X18) @ (k1_tarski @ X19))
% 0.19/0.48            = (k1_tarski @ X18))
% 0.19/0.48          | ((X18) = (X19)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.19/0.48  thf(t65_zfmisc_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.19/0.48       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.19/0.48  thf('41', plain,
% 0.19/0.48      (![X20 : $i, X21 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X20 @ X21)
% 0.19/0.48          | ((k4_xboole_0 @ X21 @ (k1_tarski @ X20)) != (X21)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.19/0.48  thf('42', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.19/0.48          | ((X0) = (X1))
% 0.19/0.48          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['40', '41'])).
% 0.19/0.48  thf('43', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X0) = (X1)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['42'])).
% 0.19/0.48  thf('44', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.19/0.48          | ((X0) = (sk_B @ (k1_tarski @ X0))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['39', '43'])).
% 0.19/0.48  thf(t69_enumset1, axiom,
% 0.19/0.48    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.48  thf('45', plain,
% 0.19/0.48      (![X14 : $i]: ((k2_tarski @ X14 @ X14) = (k1_tarski @ X14))),
% 0.19/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.48  thf(t3_boole, axiom,
% 0.19/0.48    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.19/0.48  thf('46', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.19/0.48      inference('cnf', [status(esa)], [t3_boole])).
% 0.19/0.48  thf(t73_zfmisc_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_xboole_0 ) ) <=>
% 0.19/0.48       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.19/0.48  thf('47', plain,
% 0.19/0.48      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.19/0.48         ((r2_hidden @ X23 @ X24)
% 0.19/0.48          | ((k4_xboole_0 @ (k2_tarski @ X23 @ X25) @ X24) != (k1_xboole_0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t73_zfmisc_1])).
% 0.19/0.48  thf('48', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (((k2_tarski @ X1 @ X0) != (k1_xboole_0))
% 0.19/0.48          | (r2_hidden @ X1 @ k1_xboole_0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['46', '47'])).
% 0.19/0.48  thf(t4_boole, axiom,
% 0.19/0.48    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.19/0.48  thf('49', plain,
% 0.19/0.48      (![X1 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X1) = (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [t4_boole])).
% 0.19/0.48  thf('50', plain,
% 0.19/0.48      (![X20 : $i, X21 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X20 @ X21)
% 0.19/0.48          | ((k4_xboole_0 @ X21 @ (k1_tarski @ X20)) != (X21)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.19/0.48  thf('51', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((k1_xboole_0) != (k1_xboole_0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['49', '50'])).
% 0.19/0.48  thf('52', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.19/0.48      inference('simplify', [status(thm)], ['51'])).
% 0.19/0.48  thf('53', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) != (k1_xboole_0))),
% 0.19/0.48      inference('clc', [status(thm)], ['48', '52'])).
% 0.19/0.48  thf('54', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['45', '53'])).
% 0.19/0.48  thf('55', plain, (![X0 : $i]: ((X0) = (sk_B @ (k1_tarski @ X0)))),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['44', '54'])).
% 0.19/0.48  thf('56', plain,
% 0.19/0.48      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.19/0.48         (((X36) = (k1_xboole_0))
% 0.19/0.48          | ~ (r2_hidden @ X37 @ X36)
% 0.19/0.48          | ((sk_B @ X36) != (k3_mcart_1 @ X38 @ X37 @ X39)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.19/0.48  thf('57', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.48         (((X0) != (k3_mcart_1 @ X3 @ X2 @ X1))
% 0.19/0.48          | ~ (r2_hidden @ X2 @ (k1_tarski @ X0))
% 0.19/0.48          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['55', '56'])).
% 0.19/0.48  thf('58', plain,
% 0.19/0.48      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.48         (((k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1)) = (k1_xboole_0))
% 0.19/0.48          | ~ (r2_hidden @ X2 @ (k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1))))),
% 0.19/0.48      inference('simplify', [status(thm)], ['57'])).
% 0.19/0.48  thf('59', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['45', '53'])).
% 0.19/0.48  thf('60', plain,
% 0.19/0.48      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.48         ~ (r2_hidden @ X2 @ (k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1)))),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['58', '59'])).
% 0.19/0.48  thf('61', plain,
% 0.19/0.48      (~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_D)) @ (k1_tarski @ sk_D))),
% 0.19/0.48      inference('sup-', [status(thm)], ['38', '60'])).
% 0.19/0.48  thf('62', plain,
% 0.19/0.48      (((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)
% 0.19/0.48         = (k2_mcart_1 @ (k1_mcart_1 @ sk_D)))),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['20', '21', '22', '23'])).
% 0.19/0.48  thf('63', plain,
% 0.19/0.48      ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))
% 0.19/0.48        | ((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))
% 0.19/0.48        | ((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('64', plain,
% 0.19/0.48      ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)))
% 0.19/0.48         <= ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))))),
% 0.19/0.48      inference('split', [status(esa)], ['63'])).
% 0.19/0.48  thf('65', plain,
% 0.19/0.48      ((((sk_D) = (k2_mcart_1 @ (k1_mcart_1 @ sk_D))))
% 0.19/0.48         <= ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))))),
% 0.19/0.48      inference('sup+', [status(thm)], ['62', '64'])).
% 0.19/0.48  thf('66', plain,
% 0.19/0.48      (((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) = (k2_mcart_1 @ sk_D))),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['29', '30', '31', '32'])).
% 0.19/0.48  thf('67', plain,
% 0.19/0.48      ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)))
% 0.19/0.48         <= ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))))),
% 0.19/0.48      inference('split', [status(esa)], ['63'])).
% 0.19/0.48  thf('68', plain,
% 0.19/0.48      ((((sk_D) = (k2_mcart_1 @ sk_D)))
% 0.19/0.48         <= ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))))),
% 0.19/0.48      inference('sup+', [status(thm)], ['66', '67'])).
% 0.19/0.48  thf('69', plain,
% 0.19/0.48      (((sk_D)
% 0.19/0.48         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D)) @ 
% 0.19/0.48            (k2_mcart_1 @ (k1_mcart_1 @ sk_D)) @ (k2_mcart_1 @ sk_D)))),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['34', '35', '36', '37'])).
% 0.19/0.48  thf('70', plain,
% 0.19/0.48      ((((sk_D)
% 0.19/0.48          = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D)) @ 
% 0.19/0.48             (k2_mcart_1 @ (k1_mcart_1 @ sk_D)) @ sk_D)))
% 0.19/0.48         <= ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))))),
% 0.19/0.48      inference('sup+', [status(thm)], ['68', '69'])).
% 0.19/0.48  thf(d3_mcart_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.19/0.48  thf('71', plain,
% 0.19/0.48      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.19/0.48         ((k3_mcart_1 @ X27 @ X28 @ X29)
% 0.19/0.48           = (k4_tarski @ (k4_tarski @ X27 @ X28) @ X29))),
% 0.19/0.48      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.19/0.48  thf(t20_mcart_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.19/0.48       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.19/0.48  thf('72', plain,
% 0.19/0.48      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.19/0.48         (((X33) != (k2_mcart_1 @ X33)) | ((X33) != (k4_tarski @ X34 @ X35)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.19/0.48  thf('73', plain,
% 0.19/0.48      (![X34 : $i, X35 : $i]:
% 0.19/0.48         ((k4_tarski @ X34 @ X35) != (k2_mcart_1 @ (k4_tarski @ X34 @ X35)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['72'])).
% 0.19/0.48  thf(t7_mcart_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.19/0.48       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.19/0.48  thf('74', plain,
% 0.19/0.48      (![X48 : $i, X50 : $i]: ((k2_mcart_1 @ (k4_tarski @ X48 @ X50)) = (X50))),
% 0.19/0.48      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.19/0.48  thf('75', plain, (![X34 : $i, X35 : $i]: ((k4_tarski @ X34 @ X35) != (X35))),
% 0.19/0.48      inference('demod', [status(thm)], ['73', '74'])).
% 0.19/0.48  thf('76', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i, X2 : $i]: ((k3_mcart_1 @ X2 @ X1 @ X0) != (X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['71', '75'])).
% 0.19/0.48  thf('77', plain, (~ (((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)))),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['70', '76'])).
% 0.19/0.48  thf('78', plain,
% 0.19/0.48      (((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)
% 0.19/0.48         = (k1_mcart_1 @ (k1_mcart_1 @ sk_D)))),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['11', '12', '13', '14'])).
% 0.19/0.48  thf('79', plain,
% 0.19/0.48      ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)))
% 0.19/0.48         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))))),
% 0.19/0.48      inference('split', [status(esa)], ['63'])).
% 0.19/0.48  thf('80', plain,
% 0.19/0.48      ((((sk_D) = (k1_mcart_1 @ (k1_mcart_1 @ sk_D))))
% 0.19/0.48         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))))),
% 0.19/0.48      inference('sup+', [status(thm)], ['78', '79'])).
% 0.19/0.48  thf('81', plain,
% 0.19/0.48      (((sk_D)
% 0.19/0.48         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D)) @ 
% 0.19/0.48            (k2_mcart_1 @ (k1_mcart_1 @ sk_D)) @ (k2_mcart_1 @ sk_D)))),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['34', '35', '36', '37'])).
% 0.19/0.48  thf('82', plain,
% 0.19/0.48      ((((sk_D)
% 0.19/0.48          = (k3_mcart_1 @ sk_D @ (k2_mcart_1 @ (k1_mcart_1 @ sk_D)) @ 
% 0.19/0.48             (k2_mcart_1 @ sk_D))))
% 0.19/0.48         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))))),
% 0.19/0.48      inference('sup+', [status(thm)], ['80', '81'])).
% 0.19/0.48  thf('83', plain, (![X0 : $i]: ((X0) = (sk_B @ (k1_tarski @ X0)))),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['44', '54'])).
% 0.19/0.48  thf('84', plain,
% 0.19/0.48      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.19/0.48         (((X36) = (k1_xboole_0))
% 0.19/0.48          | ~ (r2_hidden @ X38 @ X36)
% 0.19/0.48          | ((sk_B @ X36) != (k3_mcart_1 @ X38 @ X37 @ X39)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.19/0.48  thf('85', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.48         (((X0) != (k3_mcart_1 @ X3 @ X2 @ X1))
% 0.19/0.48          | ~ (r2_hidden @ X3 @ (k1_tarski @ X0))
% 0.19/0.48          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['83', '84'])).
% 0.19/0.48  thf('86', plain,
% 0.19/0.48      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.48         (((k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1)) = (k1_xboole_0))
% 0.19/0.48          | ~ (r2_hidden @ X3 @ (k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1))))),
% 0.19/0.48      inference('simplify', [status(thm)], ['85'])).
% 0.19/0.48  thf('87', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['45', '53'])).
% 0.19/0.48  thf('88', plain,
% 0.19/0.48      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.48         ~ (r2_hidden @ X3 @ (k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1)))),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['86', '87'])).
% 0.19/0.48  thf('89', plain,
% 0.19/0.48      ((~ (r2_hidden @ sk_D @ (k1_tarski @ sk_D)))
% 0.19/0.48         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['82', '88'])).
% 0.19/0.48  thf('90', plain,
% 0.19/0.48      (![X21 : $i, X22 : $i]:
% 0.19/0.48         (((k4_xboole_0 @ X21 @ (k1_tarski @ X22)) = (X21))
% 0.19/0.48          | (r2_hidden @ X22 @ X21))),
% 0.19/0.48      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.19/0.48  thf('91', plain,
% 0.19/0.48      (![X17 : $i, X18 : $i]:
% 0.19/0.48         (((X18) != (X17))
% 0.19/0.48          | ((k4_xboole_0 @ (k1_tarski @ X18) @ (k1_tarski @ X17))
% 0.19/0.48              != (k1_tarski @ X18)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.19/0.48  thf('92', plain,
% 0.19/0.48      (![X17 : $i]:
% 0.19/0.48         ((k4_xboole_0 @ (k1_tarski @ X17) @ (k1_tarski @ X17))
% 0.19/0.48           != (k1_tarski @ X17))),
% 0.19/0.48      inference('simplify', [status(thm)], ['91'])).
% 0.19/0.48  thf('93', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.19/0.48          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['90', '92'])).
% 0.19/0.48  thf('94', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.19/0.48      inference('simplify', [status(thm)], ['93'])).
% 0.19/0.48  thf('95', plain, (~ (((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)))),
% 0.19/0.48      inference('demod', [status(thm)], ['89', '94'])).
% 0.19/0.48  thf('96', plain,
% 0.19/0.48      ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))) | 
% 0.19/0.48       (((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))) | 
% 0.19/0.48       (((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)))),
% 0.19/0.48      inference('split', [status(esa)], ['63'])).
% 0.19/0.48  thf('97', plain, ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)))),
% 0.19/0.48      inference('sat_resolution*', [status(thm)], ['77', '95', '96'])).
% 0.19/0.48  thf('98', plain, (((sk_D) = (k2_mcart_1 @ (k1_mcart_1 @ sk_D)))),
% 0.19/0.48      inference('simpl_trail', [status(thm)], ['65', '97'])).
% 0.19/0.48  thf('99', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.19/0.48      inference('simplify', [status(thm)], ['93'])).
% 0.19/0.48  thf('100', plain, ($false),
% 0.19/0.48      inference('demod', [status(thm)], ['61', '98', '99'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
