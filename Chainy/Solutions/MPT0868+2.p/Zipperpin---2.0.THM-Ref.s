%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0868+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.16OepvlxLf

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:03 EST 2020

% Result     : Theorem 43.31s
% Output     : Refutation 43.31s
% Verified   : 
% Statistics : Number of formulae       :   48 (  88 expanded)
%              Number of leaves         :   15 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :  298 ( 760 expanded)
%              Number of equality atoms :   61 ( 161 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_A_14_type,type,(
    sk_A_14: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_93_type,type,(
    sk_C_93: $i )).

thf(sk_B_73_type,type,(
    sk_B_73: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(t26_mcart_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ! [C: $i] :
              ( ( m1_subset_1 @ ( C @ ( k2_zfmisc_1 @ ( A @ B ) ) ) )
             => ( ( C
                 != ( k1_mcart_1 @ C ) )
                & ( C
                 != ( k2_mcart_1 @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ~ ! [C: $i] :
                ( ( m1_subset_1 @ ( C @ ( k2_zfmisc_1 @ ( A @ B ) ) ) )
               => ( ( C
                   != ( k1_mcart_1 @ C ) )
                  & ( C
                   != ( k2_mcart_1 @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t26_mcart_1])).

thf('0',plain,
    ( ( sk_C_93
      = ( k1_mcart_1 @ sk_C_93 ) )
    | ( sk_C_93
      = ( k2_mcart_1 @ sk_C_93 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_C_93
      = ( k2_mcart_1 @ sk_C_93 ) )
   <= ( sk_C_93
      = ( k2_mcart_1 @ sk_C_93 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ ( sk_C_93 @ ( k2_zfmisc_1 @ ( sk_A_14 @ sk_B_73 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ! [C: $i] :
              ( ( m1_subset_1 @ ( C @ ( k2_zfmisc_1 @ ( A @ B ) ) ) )
             => ( C
                = ( k4_tarski @ ( k1_mcart_1 @ C @ ( k2_mcart_1 @ C ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X3894: $i,X3895: $i,X3896: $i] :
      ( ( X3894 = k1_xboole_0 )
      | ( X3895
        = ( k4_tarski @ ( k1_mcart_1 @ X3895 @ ( k2_mcart_1 @ X3895 ) ) ) )
      | ~ ( m1_subset_1 @ ( X3895 @ ( k2_zfmisc_1 @ ( X3894 @ X3896 ) ) ) )
      | ( X3896 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t24_mcart_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('4',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('5',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('6',plain,(
    ! [X3894: $i,X3895: $i,X3896: $i] :
      ( ( X3894 = o_0_0_xboole_0 )
      | ( X3895
        = ( k4_tarski @ ( k1_mcart_1 @ X3895 @ ( k2_mcart_1 @ X3895 ) ) ) )
      | ~ ( m1_subset_1 @ ( X3895 @ ( k2_zfmisc_1 @ ( X3894 @ X3896 ) ) ) )
      | ( X3896 = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,
    ( ( sk_B_73 = o_0_0_xboole_0 )
    | ( sk_C_93
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C_93 @ ( k2_mcart_1 @ sk_C_93 ) ) ) )
    | ( sk_A_14 = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','6'])).

thf('8',plain,(
    sk_A_14 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('10',plain,(
    sk_A_14 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    sk_B_73 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('13',plain,(
    sk_B_73 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( sk_C_93
    = ( k4_tarski @ ( k1_mcart_1 @ sk_C_93 @ ( k2_mcart_1 @ sk_C_93 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['7','10','13'])).

thf('15',plain,
    ( ( sk_C_93
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C_93 @ sk_C_93 ) ) )
   <= ( sk_C_93
      = ( k2_mcart_1 @ sk_C_93 ) ) ),
    inference('sup+',[status(thm)],['1','14'])).

thf(t20_mcart_1,axiom,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ ( B @ C ) ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf('16',plain,(
    ! [X3889: $i,X3890: $i,X3891: $i] :
      ( ( X3889
       != ( k2_mcart_1 @ X3889 ) )
      | ( X3889
       != ( k4_tarski @ ( X3890 @ X3891 ) ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('17',plain,(
    ! [X3890: $i,X3891: $i] :
      ( ( k4_tarski @ ( X3890 @ X3891 ) )
     != ( k2_mcart_1 @ ( k4_tarski @ ( X3890 @ X3891 ) ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ ( A @ B ) ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ ( A @ B ) ) )
        = A ) ) )).

thf('18',plain,(
    ! [X3921: $i,X3923: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ ( X3921 @ X3923 ) ) )
      = X3923 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('19',plain,(
    ! [X3890: $i,X3891: $i] :
      ( ( k4_tarski @ ( X3890 @ X3891 ) )
     != X3891 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( $false
   <= ( sk_C_93
      = ( k2_mcart_1 @ sk_C_93 ) ) ),
    inference('simplify_reflect-',[status(thm)],['15','19'])).

thf('21',plain,
    ( ( sk_C_93
      = ( k1_mcart_1 @ sk_C_93 ) )
   <= ( sk_C_93
      = ( k1_mcart_1 @ sk_C_93 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( sk_C_93
    = ( k4_tarski @ ( k1_mcart_1 @ sk_C_93 @ ( k2_mcart_1 @ sk_C_93 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['7','10','13'])).

thf('23',plain,
    ( ( sk_C_93
      = ( k4_tarski @ ( sk_C_93 @ ( k2_mcart_1 @ sk_C_93 ) ) ) )
   <= ( sk_C_93
      = ( k1_mcart_1 @ sk_C_93 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X3889: $i,X3890: $i,X3891: $i] :
      ( ( X3889
       != ( k1_mcart_1 @ X3889 ) )
      | ( X3889
       != ( k4_tarski @ ( X3890 @ X3891 ) ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('25',plain,(
    ! [X3890: $i,X3891: $i] :
      ( ( k4_tarski @ ( X3890 @ X3891 ) )
     != ( k1_mcart_1 @ ( k4_tarski @ ( X3890 @ X3891 ) ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X3921: $i,X3922: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ ( X3921 @ X3922 ) ) )
      = X3921 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('27',plain,(
    ! [X3890: $i,X3891: $i] :
      ( ( k4_tarski @ ( X3890 @ X3891 ) )
     != X3890 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    sk_C_93
 != ( k1_mcart_1 @ sk_C_93 ) ),
    inference('simplify_reflect-',[status(thm)],['23','27'])).

thf('29',plain,
    ( ( sk_C_93
      = ( k2_mcart_1 @ sk_C_93 ) )
    | ( sk_C_93
      = ( k1_mcart_1 @ sk_C_93 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('30',plain,
    ( sk_C_93
    = ( k2_mcart_1 @ sk_C_93 ) ),
    inference('sat_resolution*',[status(thm)],['28','29'])).

thf('31',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['20','30'])).

%------------------------------------------------------------------------------
