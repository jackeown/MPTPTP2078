%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0906+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5ARr1PJktk

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:04 EST 2020

% Result     : Theorem 7.87s
% Output     : Refutation 7.87s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 216 expanded)
%              Number of leaves         :   22 (  73 expanded)
%              Depth                    :   16
%              Number of atoms          :  359 (1630 expanded)
%              Number of equality atoms :   55 ( 220 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_D_11_type,type,(
    sk_D_11: $i > $i )).

thf(sk_E_3_type,type,(
    sk_E_3: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_93_type,type,(
    sk_C_93: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_79_type,type,(
    sk_B_79: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_A_14_type,type,(
    sk_A_14: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t66_mcart_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ ( A @ B ) )
       != k1_xboole_0 )
     => ! [C: $i] :
          ( ( m1_subset_1 @ ( C @ ( k2_zfmisc_1 @ ( A @ B ) ) ) )
         => ( ( C
             != ( k1_mcart_1 @ C ) )
            & ( C
             != ( k2_mcart_1 @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_zfmisc_1 @ ( A @ B ) )
         != k1_xboole_0 )
       => ! [C: $i] :
            ( ( m1_subset_1 @ ( C @ ( k2_zfmisc_1 @ ( A @ B ) ) ) )
           => ( ( C
               != ( k1_mcart_1 @ C ) )
              & ( C
               != ( k2_mcart_1 @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_mcart_1])).

thf('0',plain,(
    m1_subset_1 @ ( sk_C_93 @ ( k2_zfmisc_1 @ ( sk_A_14 @ sk_B_79 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ ( B @ A ) )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ ( B @ A ) )
        <=> ( r2_hidden @ ( B @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X1483: $i,X1484: $i] :
      ( ~ ( m1_subset_1 @ ( X1483 @ X1484 ) )
      | ( r2_hidden @ ( X1483 @ X1484 ) )
      | ( v1_xboole_0 @ X1484 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( sk_A_14 @ sk_B_79 ) ) )
    | ( r2_hidden @ ( sk_C_93 @ ( k2_zfmisc_1 @ ( sk_A_14 @ sk_B_79 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('3',plain,(
    ! [X392: $i,X393: $i] :
      ( ~ ( v1_xboole_0 @ X392 )
      | ~ ( v1_xboole_0 @ X393 )
      | ( X392 = X393 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('4',plain,(
    ( k2_zfmisc_1 @ ( sk_A_14 @ sk_B_79 ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('5',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('6',plain,(
    ( k2_zfmisc_1 @ ( sk_A_14 @ sk_B_79 ) )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( X0 != o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( sk_A_14 @ sk_B_79 ) ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,
    ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( sk_A_14 @ sk_B_79 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('9',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('10',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('11',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( sk_A_14 @ sk_B_79 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['8','11'])).

thf('13',plain,(
    r2_hidden @ ( sk_C_93 @ ( k2_zfmisc_1 @ ( sk_A_14 @ sk_B_79 ) ) ) ),
    inference(clc,[status(thm)],['2','12'])).

thf(l139_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ ( A @ ( k2_zfmisc_1 @ ( B @ C ) ) ) )
        & ! [D: $i,E: $i] :
            ( ( k4_tarski @ ( D @ E ) )
           != A ) ) )).

thf('14',plain,(
    ! [X1015: $i,X1016: $i,X1017: $i] :
      ( ( ( k4_tarski @ ( sk_D_11 @ X1015 @ ( sk_E_3 @ X1015 ) ) )
        = X1015 )
      | ~ ( r2_hidden @ ( X1015 @ ( k2_zfmisc_1 @ ( X1016 @ X1017 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('15',plain,
    ( ( k4_tarski @ ( sk_D_11 @ sk_C_93 @ ( sk_E_3 @ sk_C_93 ) ) )
    = sk_C_93 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k4_tarski @ ( sk_D_11 @ sk_C_93 @ ( sk_E_3 @ sk_C_93 ) ) )
    = sk_C_93 ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ ( A @ B ) ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ ( A @ B ) ) )
        = A ) ) )).

thf('17',plain,(
    ! [X4227: $i,X4228: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ ( X4227 @ X4228 ) ) )
      = X4227 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('18',plain,
    ( ( k1_mcart_1 @ sk_C_93 )
    = ( sk_D_11 @ sk_C_93 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_C_93 @ ( sk_E_3 @ sk_C_93 ) ) )
    = sk_C_93 ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X4227: $i,X4229: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ ( X4227 @ X4229 ) ) )
      = X4229 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('21',plain,
    ( ( k2_mcart_1 @ sk_C_93 )
    = ( sk_E_3 @ sk_C_93 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_C_93
      = ( k1_mcart_1 @ sk_C_93 ) )
    | ( sk_C_93
      = ( k2_mcart_1 @ sk_C_93 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( sk_C_93
      = ( k2_mcart_1 @ sk_C_93 ) )
   <= ( sk_C_93
      = ( k2_mcart_1 @ sk_C_93 ) ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,
    ( ( sk_C_93
      = ( k1_mcart_1 @ sk_C_93 ) )
   <= ( sk_C_93
      = ( k1_mcart_1 @ sk_C_93 ) ) ),
    inference(split,[status(esa)],['22'])).

thf('25',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_C_93 @ ( sk_E_3 @ sk_C_93 ) ) )
    = sk_C_93 ),
    inference(demod,[status(thm)],['15','18'])).

thf('26',plain,
    ( ( ( k4_tarski @ ( sk_C_93 @ ( sk_E_3 @ sk_C_93 ) ) )
      = sk_C_93 )
   <= ( sk_C_93
      = ( k1_mcart_1 @ sk_C_93 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t20_mcart_1,axiom,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ ( B @ C ) ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf('27',plain,(
    ! [X4008: $i,X4009: $i,X4010: $i] :
      ( ( X4008
       != ( k1_mcart_1 @ X4008 ) )
      | ( X4008
       != ( k4_tarski @ ( X4009 @ X4010 ) ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('28',plain,(
    ! [X4009: $i,X4010: $i] :
      ( ( k4_tarski @ ( X4009 @ X4010 ) )
     != ( k1_mcart_1 @ ( k4_tarski @ ( X4009 @ X4010 ) ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X4227: $i,X4228: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ ( X4227 @ X4228 ) ) )
      = X4227 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('30',plain,(
    ! [X4009: $i,X4010: $i] :
      ( ( k4_tarski @ ( X4009 @ X4010 ) )
     != X4009 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    sk_C_93
 != ( k1_mcart_1 @ sk_C_93 ) ),
    inference('simplify_reflect-',[status(thm)],['26','30'])).

thf('32',plain,
    ( ( sk_C_93
      = ( k2_mcart_1 @ sk_C_93 ) )
    | ( sk_C_93
      = ( k1_mcart_1 @ sk_C_93 ) ) ),
    inference(split,[status(esa)],['22'])).

thf('33',plain,
    ( sk_C_93
    = ( k2_mcart_1 @ sk_C_93 ) ),
    inference('sat_resolution*',[status(thm)],['31','32'])).

thf('34',plain,
    ( sk_C_93
    = ( k2_mcart_1 @ sk_C_93 ) ),
    inference(simpl_trail,[status(thm)],['23','33'])).

thf('35',plain,
    ( sk_C_93
    = ( sk_E_3 @ sk_C_93 ) ),
    inference(demod,[status(thm)],['21','34'])).

thf('36',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_C_93 @ ( sk_E_3 @ sk_C_93 ) ) )
    = sk_C_93 ),
    inference(demod,[status(thm)],['15','18'])).

thf('37',plain,(
    ! [X4008: $i,X4009: $i,X4010: $i] :
      ( ( X4008
       != ( k2_mcart_1 @ X4008 ) )
      | ( X4008
       != ( k4_tarski @ ( X4009 @ X4010 ) ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('38',plain,(
    ! [X4009: $i,X4010: $i] :
      ( ( k4_tarski @ ( X4009 @ X4010 ) )
     != ( k2_mcart_1 @ ( k4_tarski @ ( X4009 @ X4010 ) ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X4227: $i,X4229: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ ( X4227 @ X4229 ) ) )
      = X4229 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('40',plain,(
    ! [X4009: $i,X4010: $i] :
      ( ( k4_tarski @ ( X4009 @ X4010 ) )
     != X4010 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    sk_C_93
 != ( sk_E_3 @ sk_C_93 ) ),
    inference('sup-',[status(thm)],['36','40'])).

thf('42',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['35','41'])).

%------------------------------------------------------------------------------
