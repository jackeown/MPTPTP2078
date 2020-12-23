%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SQpI8NCCKS

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:33 EST 2020

% Result     : Theorem 19.36s
% Output     : Refutation 19.36s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 330 expanded)
%              Number of leaves         :   24 ( 110 expanded)
%              Depth                    :   11
%              Number of atoms          :  901 (6904 expanded)
%              Number of equality atoms :  120 (1104 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_C_8_type,type,(
    sk_C_8: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_B_8_type,type,(
    sk_B_8: $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

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
    m1_subset_1 @ sk_D_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_8 @ sk_C_8 ) ),
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
    ! [X222: $i,X223: $i,X224: $i,X225: $i] :
      ( ( X222 = k1_xboole_0 )
      | ( X223 = k1_xboole_0 )
      | ( X225
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X222 @ X223 @ X224 @ X225 ) @ ( k6_mcart_1 @ X222 @ X223 @ X224 @ X225 ) @ ( k7_mcart_1 @ X222 @ X223 @ X224 @ X225 ) ) )
      | ~ ( m1_subset_1 @ X225 @ ( k3_zfmisc_1 @ X222 @ X223 @ X224 ) )
      | ( X224 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t48_mcart_1])).

thf('2',plain,
    ( ( sk_C_8 = k1_xboole_0 )
    | ( sk_D_2
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2 ) @ ( k6_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2 ) @ ( k7_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2 ) ) )
    | ( sk_B_8 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    sk_B_8 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_C_8 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( sk_D_2
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2 ) @ ( k6_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2 ) @ ( k7_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_8 @ sk_C_8 ) ),
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

thf('8',plain,(
    ! [X229: $i,X230: $i,X231: $i,X232: $i] :
      ( ( X229 = k1_xboole_0 )
      | ( X230 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X229 @ X230 @ X232 @ X231 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X231 ) ) )
      | ~ ( m1_subset_1 @ X231 @ ( k3_zfmisc_1 @ X229 @ X230 @ X232 ) )
      | ( X232 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('9',plain,
    ( ( sk_C_8 = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2 )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) )
    | ( sk_B_8 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    sk_B_8 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    sk_C_8 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2 )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['9','10','11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_8 @ sk_C_8 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X229: $i,X230: $i,X231: $i,X232: $i] :
      ( ( X229 = k1_xboole_0 )
      | ( X230 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X229 @ X230 @ X232 @ X231 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X231 ) ) )
      | ~ ( m1_subset_1 @ X231 @ ( k3_zfmisc_1 @ X229 @ X230 @ X232 ) )
      | ( X232 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('16',plain,
    ( ( sk_C_8 = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2 )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) )
    | ( sk_B_8 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    sk_B_8 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    sk_C_8 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2 )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['16','17','18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_8 @ sk_C_8 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X229: $i,X230: $i,X231: $i,X232: $i] :
      ( ( X229 = k1_xboole_0 )
      | ( X230 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X229 @ X230 @ X232 @ X231 )
        = ( k2_mcart_1 @ X231 ) )
      | ~ ( m1_subset_1 @ X231 @ ( k3_zfmisc_1 @ X229 @ X230 @ X232 ) )
      | ( X232 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('23',plain,
    ( ( sk_C_8 = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2 )
      = ( k2_mcart_1 @ sk_D_2 ) )
    | ( sk_B_8 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    sk_B_8 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    sk_C_8 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2 )
    = ( k2_mcart_1 @ sk_D_2 ) ),
    inference('simplify_reflect-',[status(thm)],['23','24','25','26'])).

thf('28',plain,
    ( sk_D_2
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) @ ( k2_mcart_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['6','13','20','27'])).

thf(t39_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) )
      = ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X207: $i,X208: $i,X209: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ X207 ) @ ( k1_tarski @ X208 ) @ ( k1_tarski @ X209 ) )
      = ( k1_tarski @ ( k3_mcart_1 @ X207 @ X208 @ X209 ) ) ) ),
    inference(cnf,[status(esa)],[t39_mcart_1])).

thf(t49_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( r1_tarski @ A @ ( k3_zfmisc_1 @ A @ B @ C ) )
          & ~ ( r1_tarski @ A @ ( k3_zfmisc_1 @ B @ C @ A ) )
          & ~ ( r1_tarski @ A @ ( k3_zfmisc_1 @ C @ A @ B ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf('30',plain,(
    ! [X226: $i,X227: $i,X228: $i] :
      ( ( X226 = k1_xboole_0 )
      | ~ ( r1_tarski @ X226 @ ( k3_zfmisc_1 @ X228 @ X226 @ X227 ) ) ) ),
    inference(cnf,[status(esa)],[t49_mcart_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('32',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('33',plain,(
    ! [X66: $i,X67: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X66 ) @ X67 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['31','34'])).

thf('36',plain,(
    ~ ( r1_tarski @ ( k1_tarski @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) ) @ ( k1_tarski @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['28','35'])).

thf('37',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2 )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['16','17','18','19'])).

thf('38',plain,
    ( ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2 ) )
    | ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2 ) )
    | ( sk_D_2
      = ( k7_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2 ) )
   <= ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2 ) ) ),
    inference(split,[status(esa)],['38'])).

thf('40',plain,
    ( ( sk_D_2
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) )
   <= ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['37','39'])).

thf('41',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2 )
    = ( k2_mcart_1 @ sk_D_2 ) ),
    inference('simplify_reflect-',[status(thm)],['23','24','25','26'])).

thf('42',plain,
    ( ( sk_D_2
      = ( k7_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2 ) )
   <= ( sk_D_2
      = ( k7_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2 ) ) ),
    inference(split,[status(esa)],['38'])).

thf('43',plain,
    ( ( sk_D_2
      = ( k2_mcart_1 @ sk_D_2 ) )
   <= ( sk_D_2
      = ( k7_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( sk_D_2
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) @ ( k2_mcart_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['6','13','20','27'])).

thf('45',plain,(
    ! [X207: $i,X208: $i,X209: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ X207 ) @ ( k1_tarski @ X208 ) @ ( k1_tarski @ X209 ) )
      = ( k1_tarski @ ( k3_mcart_1 @ X207 @ X208 @ X209 ) ) ) ),
    inference(cnf,[status(esa)],[t39_mcart_1])).

thf('46',plain,(
    ! [X226: $i,X227: $i,X228: $i] :
      ( ( X226 = k1_xboole_0 )
      | ~ ( r1_tarski @ X226 @ ( k3_zfmisc_1 @ X227 @ X228 @ X226 ) ) ) ),
    inference(cnf,[status(esa)],[t49_mcart_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( r1_tarski @ ( k1_tarski @ ( k2_mcart_1 @ sk_D_2 ) ) @ ( k1_tarski @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_D_2 ) @ ( k1_tarski @ sk_D_2 ) )
   <= ( sk_D_2
      = ( k7_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['43','50'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('52',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ( X11 != X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('53',plain,(
    ! [X12: $i] :
      ( r1_tarski @ X12 @ X12 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    sk_D_2
 != ( k7_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['51','53'])).

thf('55',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2 )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['9','10','11','12'])).

thf('56',plain,
    ( ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2 ) )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2 ) ) ),
    inference(split,[status(esa)],['38'])).

thf('57',plain,
    ( ( sk_D_2
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,
    ( sk_D_2
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) @ ( k2_mcart_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['6','13','20','27'])).

thf('59',plain,(
    ! [X207: $i,X208: $i,X209: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ X207 ) @ ( k1_tarski @ X208 ) @ ( k1_tarski @ X209 ) )
      = ( k1_tarski @ ( k3_mcart_1 @ X207 @ X208 @ X209 ) ) ) ),
    inference(cnf,[status(esa)],[t39_mcart_1])).

thf('60',plain,(
    ! [X226: $i,X227: $i,X228: $i] :
      ( ( X226 = k1_xboole_0 )
      | ~ ( r1_tarski @ X226 @ ( k3_zfmisc_1 @ X226 @ X227 @ X228 ) ) ) ),
    inference(cnf,[status(esa)],[t49_mcart_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X2 ) @ ( k1_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) ) )
      | ( ( k1_tarski @ X2 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X2 ) @ ( k1_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['61','62'])).

thf('64',plain,(
    ~ ( r1_tarski @ ( k1_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) ) @ ( k1_tarski @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['58','63'])).

thf('65',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_D_2 ) @ ( k1_tarski @ sk_D_2 ) )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['57','64'])).

thf('66',plain,(
    ! [X12: $i] :
      ( r1_tarski @ X12 @ X12 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('67',plain,(
    sk_D_2
 != ( k5_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2 ) )
    | ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2 ) )
    | ( sk_D_2
      = ( k7_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2 ) ) ),
    inference(split,[status(esa)],['38'])).

thf('69',plain,
    ( sk_D_2
    = ( k6_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2 ) ),
    inference('sat_resolution*',[status(thm)],['54','67','68'])).

thf('70',plain,
    ( sk_D_2
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_2 ) ) ),
    inference(simpl_trail,[status(thm)],['40','69'])).

thf('71',plain,(
    ! [X12: $i] :
      ( r1_tarski @ X12 @ X12 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('72',plain,(
    $false ),
    inference(demod,[status(thm)],['36','70','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SQpI8NCCKS
% 0.13/0.36  % Computer   : n008.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 16:07:45 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.22/0.37  % Python version: Python 3.6.8
% 0.22/0.37  % Running in FO mode
% 19.36/19.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 19.36/19.59  % Solved by: fo/fo7.sh
% 19.36/19.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 19.36/19.59  % done 19672 iterations in 19.112s
% 19.36/19.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 19.36/19.59  % SZS output start Refutation
% 19.36/19.59  thf(sk_D_2_type, type, sk_D_2: $i).
% 19.36/19.59  thf(sk_C_8_type, type, sk_C_8: $i).
% 19.36/19.59  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 19.36/19.59  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 19.36/19.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 19.36/19.59  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 19.36/19.59  thf(sk_A_type, type, sk_A: $i).
% 19.36/19.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 19.36/19.59  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 19.36/19.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 19.36/19.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 19.36/19.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 19.36/19.59  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 19.36/19.59  thf(sk_B_8_type, type, sk_B_8: $i).
% 19.36/19.59  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 19.36/19.59  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 19.36/19.59  thf(t51_mcart_1, conjecture,
% 19.36/19.59    (![A:$i,B:$i,C:$i]:
% 19.36/19.59     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 19.36/19.59          ( ( C ) != ( k1_xboole_0 ) ) & 
% 19.36/19.59          ( ~( ![D:$i]:
% 19.36/19.59               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 19.36/19.59                 ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 19.36/19.59                   ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 19.36/19.59                   ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 19.36/19.59  thf(zf_stmt_0, negated_conjecture,
% 19.36/19.59    (~( ![A:$i,B:$i,C:$i]:
% 19.36/19.59        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 19.36/19.59             ( ( C ) != ( k1_xboole_0 ) ) & 
% 19.36/19.59             ( ~( ![D:$i]:
% 19.36/19.59                  ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 19.36/19.59                    ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 19.36/19.59                      ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 19.36/19.59                      ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ) )),
% 19.36/19.59    inference('cnf.neg', [status(esa)], [t51_mcart_1])).
% 19.36/19.59  thf('0', plain,
% 19.36/19.59      ((m1_subset_1 @ sk_D_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_8 @ sk_C_8))),
% 19.36/19.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.59  thf(t48_mcart_1, axiom,
% 19.36/19.59    (![A:$i,B:$i,C:$i]:
% 19.36/19.59     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 19.36/19.59          ( ( C ) != ( k1_xboole_0 ) ) & 
% 19.36/19.59          ( ~( ![D:$i]:
% 19.36/19.59               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 19.36/19.59                 ( ( D ) =
% 19.36/19.59                   ( k3_mcart_1 @
% 19.36/19.59                     ( k5_mcart_1 @ A @ B @ C @ D ) @ 
% 19.36/19.59                     ( k6_mcart_1 @ A @ B @ C @ D ) @ 
% 19.36/19.59                     ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 19.36/19.59  thf('1', plain,
% 19.36/19.59      (![X222 : $i, X223 : $i, X224 : $i, X225 : $i]:
% 19.36/19.59         (((X222) = (k1_xboole_0))
% 19.36/19.59          | ((X223) = (k1_xboole_0))
% 19.36/19.59          | ((X225)
% 19.36/19.59              = (k3_mcart_1 @ (k5_mcart_1 @ X222 @ X223 @ X224 @ X225) @ 
% 19.36/19.59                 (k6_mcart_1 @ X222 @ X223 @ X224 @ X225) @ 
% 19.36/19.59                 (k7_mcart_1 @ X222 @ X223 @ X224 @ X225)))
% 19.36/19.59          | ~ (m1_subset_1 @ X225 @ (k3_zfmisc_1 @ X222 @ X223 @ X224))
% 19.36/19.59          | ((X224) = (k1_xboole_0)))),
% 19.36/19.59      inference('cnf', [status(esa)], [t48_mcart_1])).
% 19.36/19.59  thf('2', plain,
% 19.36/19.59      ((((sk_C_8) = (k1_xboole_0))
% 19.36/19.59        | ((sk_D_2)
% 19.36/19.59            = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2) @ 
% 19.36/19.59               (k6_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2) @ 
% 19.36/19.59               (k7_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2)))
% 19.36/19.59        | ((sk_B_8) = (k1_xboole_0))
% 19.36/19.59        | ((sk_A) = (k1_xboole_0)))),
% 19.36/19.59      inference('sup-', [status(thm)], ['0', '1'])).
% 19.36/19.59  thf('3', plain, (((sk_A) != (k1_xboole_0))),
% 19.36/19.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.59  thf('4', plain, (((sk_B_8) != (k1_xboole_0))),
% 19.36/19.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.59  thf('5', plain, (((sk_C_8) != (k1_xboole_0))),
% 19.36/19.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.59  thf('6', plain,
% 19.36/19.59      (((sk_D_2)
% 19.36/19.59         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2) @ 
% 19.36/19.59            (k6_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2) @ 
% 19.36/19.59            (k7_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2)))),
% 19.36/19.59      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5'])).
% 19.36/19.59  thf('7', plain,
% 19.36/19.59      ((m1_subset_1 @ sk_D_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_8 @ sk_C_8))),
% 19.36/19.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.59  thf(t50_mcart_1, axiom,
% 19.36/19.59    (![A:$i,B:$i,C:$i]:
% 19.36/19.59     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 19.36/19.59          ( ( C ) != ( k1_xboole_0 ) ) & 
% 19.36/19.59          ( ~( ![D:$i]:
% 19.36/19.59               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 19.36/19.59                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 19.36/19.59                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 19.36/19.59                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 19.36/19.59                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 19.36/19.59                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 19.36/19.59  thf('8', plain,
% 19.36/19.59      (![X229 : $i, X230 : $i, X231 : $i, X232 : $i]:
% 19.36/19.59         (((X229) = (k1_xboole_0))
% 19.36/19.59          | ((X230) = (k1_xboole_0))
% 19.36/19.59          | ((k5_mcart_1 @ X229 @ X230 @ X232 @ X231)
% 19.36/19.59              = (k1_mcart_1 @ (k1_mcart_1 @ X231)))
% 19.36/19.59          | ~ (m1_subset_1 @ X231 @ (k3_zfmisc_1 @ X229 @ X230 @ X232))
% 19.36/19.59          | ((X232) = (k1_xboole_0)))),
% 19.36/19.59      inference('cnf', [status(esa)], [t50_mcart_1])).
% 19.36/19.59  thf('9', plain,
% 19.36/19.59      ((((sk_C_8) = (k1_xboole_0))
% 19.36/19.59        | ((k5_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2)
% 19.36/19.59            = (k1_mcart_1 @ (k1_mcart_1 @ sk_D_2)))
% 19.36/19.59        | ((sk_B_8) = (k1_xboole_0))
% 19.36/19.59        | ((sk_A) = (k1_xboole_0)))),
% 19.36/19.59      inference('sup-', [status(thm)], ['7', '8'])).
% 19.36/19.59  thf('10', plain, (((sk_A) != (k1_xboole_0))),
% 19.36/19.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.59  thf('11', plain, (((sk_B_8) != (k1_xboole_0))),
% 19.36/19.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.59  thf('12', plain, (((sk_C_8) != (k1_xboole_0))),
% 19.36/19.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.59  thf('13', plain,
% 19.36/19.59      (((k5_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2)
% 19.36/19.59         = (k1_mcart_1 @ (k1_mcart_1 @ sk_D_2)))),
% 19.36/19.59      inference('simplify_reflect-', [status(thm)], ['9', '10', '11', '12'])).
% 19.36/19.59  thf('14', plain,
% 19.36/19.59      ((m1_subset_1 @ sk_D_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_8 @ sk_C_8))),
% 19.36/19.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.59  thf('15', plain,
% 19.36/19.59      (![X229 : $i, X230 : $i, X231 : $i, X232 : $i]:
% 19.36/19.59         (((X229) = (k1_xboole_0))
% 19.36/19.59          | ((X230) = (k1_xboole_0))
% 19.36/19.59          | ((k6_mcart_1 @ X229 @ X230 @ X232 @ X231)
% 19.36/19.59              = (k2_mcart_1 @ (k1_mcart_1 @ X231)))
% 19.36/19.59          | ~ (m1_subset_1 @ X231 @ (k3_zfmisc_1 @ X229 @ X230 @ X232))
% 19.36/19.59          | ((X232) = (k1_xboole_0)))),
% 19.36/19.59      inference('cnf', [status(esa)], [t50_mcart_1])).
% 19.36/19.59  thf('16', plain,
% 19.36/19.59      ((((sk_C_8) = (k1_xboole_0))
% 19.36/19.59        | ((k6_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2)
% 19.36/19.59            = (k2_mcart_1 @ (k1_mcart_1 @ sk_D_2)))
% 19.36/19.59        | ((sk_B_8) = (k1_xboole_0))
% 19.36/19.59        | ((sk_A) = (k1_xboole_0)))),
% 19.36/19.59      inference('sup-', [status(thm)], ['14', '15'])).
% 19.36/19.59  thf('17', plain, (((sk_A) != (k1_xboole_0))),
% 19.36/19.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.59  thf('18', plain, (((sk_B_8) != (k1_xboole_0))),
% 19.36/19.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.59  thf('19', plain, (((sk_C_8) != (k1_xboole_0))),
% 19.36/19.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.59  thf('20', plain,
% 19.36/19.59      (((k6_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2)
% 19.36/19.59         = (k2_mcart_1 @ (k1_mcart_1 @ sk_D_2)))),
% 19.36/19.59      inference('simplify_reflect-', [status(thm)], ['16', '17', '18', '19'])).
% 19.36/19.59  thf('21', plain,
% 19.36/19.59      ((m1_subset_1 @ sk_D_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_8 @ sk_C_8))),
% 19.36/19.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.59  thf('22', plain,
% 19.36/19.59      (![X229 : $i, X230 : $i, X231 : $i, X232 : $i]:
% 19.36/19.59         (((X229) = (k1_xboole_0))
% 19.36/19.59          | ((X230) = (k1_xboole_0))
% 19.36/19.59          | ((k7_mcart_1 @ X229 @ X230 @ X232 @ X231) = (k2_mcart_1 @ X231))
% 19.36/19.59          | ~ (m1_subset_1 @ X231 @ (k3_zfmisc_1 @ X229 @ X230 @ X232))
% 19.36/19.59          | ((X232) = (k1_xboole_0)))),
% 19.36/19.59      inference('cnf', [status(esa)], [t50_mcart_1])).
% 19.36/19.59  thf('23', plain,
% 19.36/19.59      ((((sk_C_8) = (k1_xboole_0))
% 19.36/19.59        | ((k7_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2)
% 19.36/19.59            = (k2_mcart_1 @ sk_D_2))
% 19.36/19.59        | ((sk_B_8) = (k1_xboole_0))
% 19.36/19.59        | ((sk_A) = (k1_xboole_0)))),
% 19.36/19.59      inference('sup-', [status(thm)], ['21', '22'])).
% 19.36/19.59  thf('24', plain, (((sk_A) != (k1_xboole_0))),
% 19.36/19.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.59  thf('25', plain, (((sk_B_8) != (k1_xboole_0))),
% 19.36/19.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.59  thf('26', plain, (((sk_C_8) != (k1_xboole_0))),
% 19.36/19.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.59  thf('27', plain,
% 19.36/19.59      (((k7_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2) = (k2_mcart_1 @ sk_D_2))),
% 19.36/19.59      inference('simplify_reflect-', [status(thm)], ['23', '24', '25', '26'])).
% 19.36/19.59  thf('28', plain,
% 19.36/19.59      (((sk_D_2)
% 19.36/19.59         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_2)) @ 
% 19.36/19.59            (k2_mcart_1 @ (k1_mcart_1 @ sk_D_2)) @ (k2_mcart_1 @ sk_D_2)))),
% 19.36/19.59      inference('demod', [status(thm)], ['6', '13', '20', '27'])).
% 19.36/19.59  thf(t39_mcart_1, axiom,
% 19.36/19.59    (![A:$i,B:$i,C:$i]:
% 19.36/19.59     ( ( k3_zfmisc_1 @
% 19.36/19.59         ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) ) =
% 19.36/19.59       ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ))).
% 19.36/19.59  thf('29', plain,
% 19.36/19.59      (![X207 : $i, X208 : $i, X209 : $i]:
% 19.36/19.59         ((k3_zfmisc_1 @ (k1_tarski @ X207) @ (k1_tarski @ X208) @ 
% 19.36/19.59           (k1_tarski @ X209))
% 19.36/19.59           = (k1_tarski @ (k3_mcart_1 @ X207 @ X208 @ X209)))),
% 19.36/19.59      inference('cnf', [status(esa)], [t39_mcart_1])).
% 19.36/19.59  thf(t49_mcart_1, axiom,
% 19.36/19.59    (![A:$i,B:$i,C:$i]:
% 19.36/19.59     ( ( ~( ( ~( r1_tarski @ A @ ( k3_zfmisc_1 @ A @ B @ C ) ) ) & 
% 19.36/19.59            ( ~( r1_tarski @ A @ ( k3_zfmisc_1 @ B @ C @ A ) ) ) & 
% 19.36/19.59            ( ~( r1_tarski @ A @ ( k3_zfmisc_1 @ C @ A @ B ) ) ) ) ) =>
% 19.36/19.59       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 19.36/19.59  thf('30', plain,
% 19.36/19.59      (![X226 : $i, X227 : $i, X228 : $i]:
% 19.36/19.59         (((X226) = (k1_xboole_0))
% 19.36/19.59          | ~ (r1_tarski @ X226 @ (k3_zfmisc_1 @ X228 @ X226 @ X227)))),
% 19.36/19.59      inference('cnf', [status(esa)], [t49_mcart_1])).
% 19.36/19.59  thf('31', plain,
% 19.36/19.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.36/19.59         (~ (r1_tarski @ (k1_tarski @ X1) @ 
% 19.36/19.59             (k1_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0)))
% 19.36/19.59          | ((k1_tarski @ X1) = (k1_xboole_0)))),
% 19.36/19.59      inference('sup-', [status(thm)], ['29', '30'])).
% 19.36/19.59  thf(idempotence_k2_xboole_0, axiom,
% 19.36/19.59    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 19.36/19.59  thf('32', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ X8) = (X8))),
% 19.36/19.59      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 19.36/19.59  thf(t49_zfmisc_1, axiom,
% 19.36/19.59    (![A:$i,B:$i]:
% 19.36/19.59     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 19.36/19.59  thf('33', plain,
% 19.36/19.59      (![X66 : $i, X67 : $i]:
% 19.36/19.59         ((k2_xboole_0 @ (k1_tarski @ X66) @ X67) != (k1_xboole_0))),
% 19.36/19.59      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 19.36/19.59  thf('34', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 19.36/19.59      inference('sup-', [status(thm)], ['32', '33'])).
% 19.36/19.59  thf('35', plain,
% 19.36/19.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.36/19.59         ~ (r1_tarski @ (k1_tarski @ X1) @ 
% 19.36/19.59            (k1_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0)))),
% 19.36/19.59      inference('simplify_reflect-', [status(thm)], ['31', '34'])).
% 19.36/19.59  thf('36', plain,
% 19.36/19.59      (~ (r1_tarski @ (k1_tarski @ (k2_mcart_1 @ (k1_mcart_1 @ sk_D_2))) @ 
% 19.36/19.59          (k1_tarski @ sk_D_2))),
% 19.36/19.59      inference('sup-', [status(thm)], ['28', '35'])).
% 19.36/19.59  thf('37', plain,
% 19.36/19.59      (((k6_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2)
% 19.36/19.59         = (k2_mcart_1 @ (k1_mcart_1 @ sk_D_2)))),
% 19.36/19.59      inference('simplify_reflect-', [status(thm)], ['16', '17', '18', '19'])).
% 19.36/19.59  thf('38', plain,
% 19.36/19.59      ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2))
% 19.36/19.59        | ((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2))
% 19.36/19.59        | ((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2)))),
% 19.36/19.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.36/19.59  thf('39', plain,
% 19.36/19.59      ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2)))
% 19.36/19.59         <= ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2))))),
% 19.36/19.59      inference('split', [status(esa)], ['38'])).
% 19.36/19.59  thf('40', plain,
% 19.36/19.59      ((((sk_D_2) = (k2_mcart_1 @ (k1_mcart_1 @ sk_D_2))))
% 19.36/19.59         <= ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2))))),
% 19.36/19.59      inference('sup+', [status(thm)], ['37', '39'])).
% 19.36/19.59  thf('41', plain,
% 19.36/19.59      (((k7_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2) = (k2_mcart_1 @ sk_D_2))),
% 19.36/19.59      inference('simplify_reflect-', [status(thm)], ['23', '24', '25', '26'])).
% 19.36/19.59  thf('42', plain,
% 19.36/19.59      ((((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2)))
% 19.36/19.59         <= ((((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2))))),
% 19.36/19.59      inference('split', [status(esa)], ['38'])).
% 19.36/19.59  thf('43', plain,
% 19.36/19.59      ((((sk_D_2) = (k2_mcart_1 @ sk_D_2)))
% 19.36/19.59         <= ((((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2))))),
% 19.36/19.59      inference('sup+', [status(thm)], ['41', '42'])).
% 19.36/19.59  thf('44', plain,
% 19.36/19.59      (((sk_D_2)
% 19.36/19.59         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_2)) @ 
% 19.36/19.59            (k2_mcart_1 @ (k1_mcart_1 @ sk_D_2)) @ (k2_mcart_1 @ sk_D_2)))),
% 19.36/19.59      inference('demod', [status(thm)], ['6', '13', '20', '27'])).
% 19.36/19.59  thf('45', plain,
% 19.36/19.59      (![X207 : $i, X208 : $i, X209 : $i]:
% 19.36/19.59         ((k3_zfmisc_1 @ (k1_tarski @ X207) @ (k1_tarski @ X208) @ 
% 19.36/19.59           (k1_tarski @ X209))
% 19.36/19.59           = (k1_tarski @ (k3_mcart_1 @ X207 @ X208 @ X209)))),
% 19.36/19.59      inference('cnf', [status(esa)], [t39_mcart_1])).
% 19.36/19.59  thf('46', plain,
% 19.36/19.59      (![X226 : $i, X227 : $i, X228 : $i]:
% 19.36/19.59         (((X226) = (k1_xboole_0))
% 19.36/19.59          | ~ (r1_tarski @ X226 @ (k3_zfmisc_1 @ X227 @ X228 @ X226)))),
% 19.36/19.59      inference('cnf', [status(esa)], [t49_mcart_1])).
% 19.36/19.59  thf('47', plain,
% 19.36/19.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.36/19.59         (~ (r1_tarski @ (k1_tarski @ X0) @ 
% 19.36/19.59             (k1_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0)))
% 19.36/19.59          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 19.36/19.59      inference('sup-', [status(thm)], ['45', '46'])).
% 19.36/19.59  thf('48', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 19.36/19.59      inference('sup-', [status(thm)], ['32', '33'])).
% 19.36/19.59  thf('49', plain,
% 19.36/19.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.36/19.59         ~ (r1_tarski @ (k1_tarski @ X0) @ 
% 19.36/19.59            (k1_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0)))),
% 19.36/19.59      inference('simplify_reflect-', [status(thm)], ['47', '48'])).
% 19.36/19.59  thf('50', plain,
% 19.36/19.59      (~ (r1_tarski @ (k1_tarski @ (k2_mcart_1 @ sk_D_2)) @ 
% 19.36/19.59          (k1_tarski @ sk_D_2))),
% 19.36/19.59      inference('sup-', [status(thm)], ['44', '49'])).
% 19.36/19.59  thf('51', plain,
% 19.36/19.59      ((~ (r1_tarski @ (k1_tarski @ sk_D_2) @ (k1_tarski @ sk_D_2)))
% 19.36/19.59         <= ((((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2))))),
% 19.36/19.59      inference('sup-', [status(thm)], ['43', '50'])).
% 19.36/19.59  thf(d10_xboole_0, axiom,
% 19.36/19.59    (![A:$i,B:$i]:
% 19.36/19.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 19.36/19.59  thf('52', plain,
% 19.36/19.59      (![X11 : $i, X12 : $i]: ((r1_tarski @ X11 @ X12) | ((X11) != (X12)))),
% 19.36/19.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 19.36/19.59  thf('53', plain, (![X12 : $i]: (r1_tarski @ X12 @ X12)),
% 19.36/19.59      inference('simplify', [status(thm)], ['52'])).
% 19.36/19.59  thf('54', plain,
% 19.36/19.59      (~ (((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2)))),
% 19.36/19.59      inference('demod', [status(thm)], ['51', '53'])).
% 19.36/19.59  thf('55', plain,
% 19.36/19.59      (((k5_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2)
% 19.36/19.59         = (k1_mcart_1 @ (k1_mcart_1 @ sk_D_2)))),
% 19.36/19.59      inference('simplify_reflect-', [status(thm)], ['9', '10', '11', '12'])).
% 19.36/19.59  thf('56', plain,
% 19.36/19.59      ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2)))
% 19.36/19.59         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2))))),
% 19.36/19.59      inference('split', [status(esa)], ['38'])).
% 19.36/19.59  thf('57', plain,
% 19.36/19.59      ((((sk_D_2) = (k1_mcart_1 @ (k1_mcart_1 @ sk_D_2))))
% 19.36/19.59         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2))))),
% 19.36/19.59      inference('sup+', [status(thm)], ['55', '56'])).
% 19.36/19.59  thf('58', plain,
% 19.36/19.59      (((sk_D_2)
% 19.36/19.59         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_2)) @ 
% 19.36/19.59            (k2_mcart_1 @ (k1_mcart_1 @ sk_D_2)) @ (k2_mcart_1 @ sk_D_2)))),
% 19.36/19.59      inference('demod', [status(thm)], ['6', '13', '20', '27'])).
% 19.36/19.59  thf('59', plain,
% 19.36/19.59      (![X207 : $i, X208 : $i, X209 : $i]:
% 19.36/19.59         ((k3_zfmisc_1 @ (k1_tarski @ X207) @ (k1_tarski @ X208) @ 
% 19.36/19.59           (k1_tarski @ X209))
% 19.36/19.59           = (k1_tarski @ (k3_mcart_1 @ X207 @ X208 @ X209)))),
% 19.36/19.59      inference('cnf', [status(esa)], [t39_mcart_1])).
% 19.36/19.59  thf('60', plain,
% 19.36/19.59      (![X226 : $i, X227 : $i, X228 : $i]:
% 19.36/19.59         (((X226) = (k1_xboole_0))
% 19.36/19.59          | ~ (r1_tarski @ X226 @ (k3_zfmisc_1 @ X226 @ X227 @ X228)))),
% 19.36/19.59      inference('cnf', [status(esa)], [t49_mcart_1])).
% 19.36/19.59  thf('61', plain,
% 19.36/19.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.36/19.59         (~ (r1_tarski @ (k1_tarski @ X2) @ 
% 19.36/19.59             (k1_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0)))
% 19.36/19.59          | ((k1_tarski @ X2) = (k1_xboole_0)))),
% 19.36/19.59      inference('sup-', [status(thm)], ['59', '60'])).
% 19.36/19.59  thf('62', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 19.36/19.59      inference('sup-', [status(thm)], ['32', '33'])).
% 19.36/19.59  thf('63', plain,
% 19.36/19.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.36/19.59         ~ (r1_tarski @ (k1_tarski @ X2) @ 
% 19.36/19.59            (k1_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0)))),
% 19.36/19.59      inference('simplify_reflect-', [status(thm)], ['61', '62'])).
% 19.36/19.59  thf('64', plain,
% 19.36/19.59      (~ (r1_tarski @ (k1_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_2))) @ 
% 19.36/19.59          (k1_tarski @ sk_D_2))),
% 19.36/19.59      inference('sup-', [status(thm)], ['58', '63'])).
% 19.36/19.59  thf('65', plain,
% 19.36/19.59      ((~ (r1_tarski @ (k1_tarski @ sk_D_2) @ (k1_tarski @ sk_D_2)))
% 19.36/19.59         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2))))),
% 19.36/19.59      inference('sup-', [status(thm)], ['57', '64'])).
% 19.36/19.59  thf('66', plain, (![X12 : $i]: (r1_tarski @ X12 @ X12)),
% 19.36/19.59      inference('simplify', [status(thm)], ['52'])).
% 19.36/19.59  thf('67', plain,
% 19.36/19.59      (~ (((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2)))),
% 19.36/19.59      inference('demod', [status(thm)], ['65', '66'])).
% 19.36/19.59  thf('68', plain,
% 19.36/19.59      ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2))) | 
% 19.36/19.59       (((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2))) | 
% 19.36/19.59       (((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2)))),
% 19.36/19.59      inference('split', [status(esa)], ['38'])).
% 19.36/19.59  thf('69', plain,
% 19.36/19.59      ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_8 @ sk_C_8 @ sk_D_2)))),
% 19.36/19.59      inference('sat_resolution*', [status(thm)], ['54', '67', '68'])).
% 19.36/19.59  thf('70', plain, (((sk_D_2) = (k2_mcart_1 @ (k1_mcart_1 @ sk_D_2)))),
% 19.36/19.59      inference('simpl_trail', [status(thm)], ['40', '69'])).
% 19.36/19.59  thf('71', plain, (![X12 : $i]: (r1_tarski @ X12 @ X12)),
% 19.36/19.59      inference('simplify', [status(thm)], ['52'])).
% 19.36/19.59  thf('72', plain, ($false),
% 19.36/19.59      inference('demod', [status(thm)], ['36', '70', '71'])).
% 19.36/19.59  
% 19.36/19.59  % SZS output end Refutation
% 19.36/19.59  
% 19.43/19.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
