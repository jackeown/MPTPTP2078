%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.25IoRDxKQj

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:32 EST 2020

% Result     : Theorem 0.82s
% Output     : Refutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :  142 (9770 expanded)
%              Number of leaves         :   27 (2786 expanded)
%              Depth                    :   40
%              Number of atoms          : 1678 (149605 expanded)
%              Number of equality atoms :   92 (6854 expanded)
%              Maximal formula depth    :   16 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

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

thf('0',plain,(
    ! [X28: $i] :
      ( ( X28 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X28 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf(t49_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( r1_tarski @ A @ ( k3_zfmisc_1 @ A @ B @ C ) )
          & ~ ( r1_tarski @ A @ ( k3_zfmisc_1 @ B @ C @ A ) )
          & ~ ( r1_tarski @ A @ ( k3_zfmisc_1 @ C @ A @ B ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ~ ( ~ ( r1_tarski @ A @ ( k3_zfmisc_1 @ A @ B @ C ) )
            & ~ ( r1_tarski @ A @ ( k3_zfmisc_1 @ B @ C @ A ) )
            & ~ ( r1_tarski @ A @ ( k3_zfmisc_1 @ C @ A @ B ) ) )
       => ( A = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t49_mcart_1])).

thf('1',plain,
    ( ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_B_1 @ sk_C_1 @ sk_A ) )
    | ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_C_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_C_1 @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_C_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['1'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k3_zfmisc_1 @ sk_C_1 @ sk_A @ sk_B_1 ) )
        | ~ ( r2_hidden @ X0 @ sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_C_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ sk_A ) @ ( k3_zfmisc_1 @ sk_C_1 @ sk_A @ sk_B_1 ) ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_C_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r2_hidden @ ( sk_B @ sk_A ) @ ( k3_zfmisc_1 @ sk_C_1 @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_C_1 @ sk_A @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_B_1 @ sk_C_1 @ sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_B_1 @ sk_C_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('9',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k3_zfmisc_1 @ X25 @ X26 @ X27 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t135_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) )
        | ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf('10',plain,(
    ! [X20: $i,X21: $i] :
      ( ( X20 = k1_xboole_0 )
      | ~ ( r1_tarski @ X20 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_B_1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ~ ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_B_1 @ sk_C_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X28: $i] :
      ( ( X28 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X28 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('16',plain,
    ( ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['1'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
        | ~ ( r2_hidden @ X0 @ sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ sk_A ) @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( r2_hidden @ ( sk_B @ sk_A ) @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k3_zfmisc_1 @ X25 @ X26 @ X27 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(d2_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( ( r2_hidden @ E @ A )
              & ( r2_hidden @ F @ B )
              & ( D
                = ( k4_tarski @ E @ F ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [F: $i,E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ D @ B @ A )
    <=> ( ( D
          = ( k4_tarski @ E @ F ) )
        & ( r2_hidden @ F @ B )
        & ( r2_hidden @ E @ A ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X16 @ X13 @ X14 ) @ ( sk_E_1 @ X16 @ X13 @ X14 ) @ X16 @ X13 @ X14 )
      | ( X15
       != ( k2_zfmisc_1 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('24',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X16 @ X13 @ X14 ) @ ( sk_E_1 @ X16 @ X13 @ X14 ) @ X16 @ X13 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k2_zfmisc_1 @ X14 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X3 @ X0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) @ ( sk_E_1 @ X3 @ X0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) @ X3 @ X0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,
    ( ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_B @ sk_A ) @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) @ ( sk_E_1 @ ( sk_B @ sk_A ) @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) @ ( sk_B @ sk_A ) @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X6
        = ( k4_tarski @ X4 @ X5 ) )
      | ~ ( zip_tseitin_0 @ X5 @ X4 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('28',plain,
    ( ( ( sk_B @ sk_A )
      = ( k4_tarski @ ( sk_E_1 @ ( sk_B @ sk_A ) @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) @ ( sk_F_1 @ ( sk_B @ sk_A ) @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( sk_B @ sk_A )
      = ( k4_tarski @ ( sk_E_1 @ ( sk_B @ sk_A ) @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) @ ( sk_F_1 @ ( sk_B @ sk_A ) @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('30',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X32 @ X33 ) )
      = X32 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('31',plain,
    ( ( ( k1_mcart_1 @ ( sk_B @ sk_A ) )
      = ( sk_E_1 @ ( sk_B @ sk_A ) @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( sk_B @ sk_A )
      = ( k4_tarski @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ ( sk_F_1 @ ( sk_B @ sk_A ) @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,
    ( ( ( sk_B @ sk_A )
      = ( k4_tarski @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ ( sk_F_1 @ ( sk_B @ sk_A ) @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('34',plain,(
    ! [X32: $i,X34: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X32 @ X34 ) )
      = X34 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('35',plain,
    ( ( ( k2_mcart_1 @ ( sk_B @ sk_A ) )
      = ( sk_F_1 @ ( sk_B @ sk_A ) @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( sk_B @ sk_A )
      = ( k4_tarski @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ ( k2_mcart_1 @ ( sk_B @ sk_A ) ) ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['32','35'])).

thf('37',plain,
    ( ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_B @ sk_A ) @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) @ ( sk_E_1 @ ( sk_B @ sk_A ) @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) @ ( sk_B @ sk_A ) @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('38',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X4 @ X8 )
      | ~ ( zip_tseitin_0 @ X5 @ X4 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('39',plain,
    ( ( r2_hidden @ ( sk_E_1 @ ( sk_B @ sk_A ) @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k1_mcart_1 @ ( sk_B @ sk_A ) )
      = ( sk_E_1 @ ( sk_B @ sk_A ) @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('41',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X16 @ X13 @ X14 ) @ ( sk_E_1 @ X16 @ X13 @ X14 ) @ X16 @ X13 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k2_zfmisc_1 @ X14 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('43',plain,
    ( ( zip_tseitin_0 @ ( sk_F_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ sk_B_1 @ sk_A ) @ ( sk_E_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ sk_B_1 @ sk_A ) @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ sk_B_1 @ sk_A )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X4 @ X8 )
      | ~ ( zip_tseitin_0 @ X5 @ X4 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('45',plain,
    ( ( r2_hidden @ ( sk_E_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ sk_B_1 @ sk_A ) @ sk_A )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( zip_tseitin_0 @ ( sk_F_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ sk_B_1 @ sk_A ) @ ( sk_E_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ sk_B_1 @ sk_A ) @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ sk_B_1 @ sk_A )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('47',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X6
        = ( k4_tarski @ X4 @ X5 ) )
      | ~ ( zip_tseitin_0 @ X5 @ X4 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('48',plain,
    ( ( ( k1_mcart_1 @ ( sk_B @ sk_A ) )
      = ( k4_tarski @ ( sk_E_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ sk_B_1 @ sk_A ) @ ( sk_F_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ sk_B_1 @ sk_A ) ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X32 @ X33 ) )
      = X32 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('50',plain,
    ( ( ( k1_mcart_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) )
      = ( sk_E_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ sk_B_1 @ sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) ) @ sk_A )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['45','50'])).

thf('52',plain,
    ( ( ( k1_mcart_1 @ ( sk_B @ sk_A ) )
      = ( k4_tarski @ ( sk_E_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ sk_B_1 @ sk_A ) @ ( sk_F_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ sk_B_1 @ sk_A ) ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('53',plain,
    ( ( ( k1_mcart_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) )
      = ( sk_E_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ sk_B_1 @ sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('54',plain,
    ( ( ( k1_mcart_1 @ ( sk_B @ sk_A ) )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) ) @ ( sk_F_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ sk_B_1 @ sk_A ) ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( k1_mcart_1 @ ( sk_B @ sk_A ) )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) ) @ ( sk_F_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ sk_B_1 @ sk_A ) ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('56',plain,(
    ! [X32: $i,X34: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X32 @ X34 ) )
      = X34 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('57',plain,
    ( ( ( k2_mcart_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) )
      = ( sk_F_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ sk_B_1 @ sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k1_mcart_1 @ ( sk_B @ sk_A ) )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) ) ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['54','57'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('59',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k3_mcart_1 @ X22 @ X23 @ X24 )
      = ( k4_tarski @ ( k4_tarski @ X22 @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('60',plain,
    ( ! [X0: $i] :
        ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) ) @ X0 )
        = ( k4_tarski @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ X0 ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( X28 = k1_xboole_0 )
      | ~ ( r2_hidden @ X30 @ X28 )
      | ( ( sk_B @ X28 )
       != ( k3_mcart_1 @ X30 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('62',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( sk_B @ X1 )
         != ( k4_tarski @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ X0 ) )
        | ~ ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) ) @ X1 )
        | ( X1 = k1_xboole_0 ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ( sk_A = k1_xboole_0 )
        | ( ( sk_B @ sk_A )
         != ( k4_tarski @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ X0 ) ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['51','62'])).

thf('64',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ! [X0: $i] :
        ( ( sk_B @ sk_A )
       != ( k4_tarski @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ X0 ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( sk_B @ sk_A )
     != ( sk_B @ sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['36','65'])).

thf('67',plain,(
    ~ ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_C_1 @ sk_A @ sk_B_1 ) )
    | ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
    | ( r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_B_1 @ sk_C_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('69',plain,(
    r1_tarski @ sk_A @ ( k3_zfmisc_1 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['14','67','68'])).

thf('70',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ ( k3_zfmisc_1 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['7','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X3 @ X0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) @ ( sk_E_1 @ X3 @ X0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) @ X3 @ X0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('72',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ ( sk_B @ sk_A ) @ sk_B_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) @ ( sk_E_1 @ ( sk_B @ sk_A ) @ sk_B_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) @ ( sk_B @ sk_A ) @ sk_B_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X6
        = ( k4_tarski @ X4 @ X5 ) )
      | ~ ( zip_tseitin_0 @ X5 @ X4 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('74',plain,
    ( ( sk_B @ sk_A )
    = ( k4_tarski @ ( sk_E_1 @ ( sk_B @ sk_A ) @ sk_B_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) @ ( sk_F_1 @ ( sk_B @ sk_A ) @ sk_B_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( sk_B @ sk_A )
    = ( k4_tarski @ ( sk_E_1 @ ( sk_B @ sk_A ) @ sk_B_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) @ ( sk_F_1 @ ( sk_B @ sk_A ) @ sk_B_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('76',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X32 @ X33 ) )
      = X32 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('77',plain,
    ( ( k1_mcart_1 @ ( sk_B @ sk_A ) )
    = ( sk_E_1 @ ( sk_B @ sk_A ) @ sk_B_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( sk_B @ sk_A )
    = ( k4_tarski @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ ( sk_F_1 @ ( sk_B @ sk_A ) @ sk_B_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['74','77'])).

thf('79',plain,
    ( ( sk_B @ sk_A )
    = ( k4_tarski @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ ( sk_F_1 @ ( sk_B @ sk_A ) @ sk_B_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['74','77'])).

thf('80',plain,(
    ! [X32: $i,X34: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X32 @ X34 ) )
      = X34 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('81',plain,
    ( ( k2_mcart_1 @ ( sk_B @ sk_A ) )
    = ( sk_F_1 @ ( sk_B @ sk_A ) @ sk_B_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( sk_B @ sk_A )
    = ( k4_tarski @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ ( k2_mcart_1 @ ( sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['78','81'])).

thf('83',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ ( sk_B @ sk_A ) @ sk_B_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) @ ( sk_E_1 @ ( sk_B @ sk_A ) @ sk_B_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) @ ( sk_B @ sk_A ) @ sk_B_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('84',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X4 @ X8 )
      | ~ ( zip_tseitin_0 @ X5 @ X4 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('85',plain,(
    r2_hidden @ ( sk_E_1 @ ( sk_B @ sk_A ) @ sk_B_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k1_mcart_1 @ ( sk_B @ sk_A ) )
    = ( sk_E_1 @ ( sk_B @ sk_A ) @ sk_B_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('87',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X16 @ X13 @ X14 ) @ ( sk_E_1 @ X16 @ X13 @ X14 ) @ X16 @ X13 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k2_zfmisc_1 @ X14 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('89',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ sk_A @ sk_C_1 ) @ ( sk_E_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ sk_A @ sk_C_1 ) @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X5 @ X7 )
      | ~ ( zip_tseitin_0 @ X5 @ X4 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('91',plain,(
    r2_hidden @ ( sk_F_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ sk_A @ sk_C_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ sk_A @ sk_C_1 ) @ ( sk_E_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ sk_A @ sk_C_1 ) @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['87','88'])).

thf('93',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X6
        = ( k4_tarski @ X4 @ X5 ) )
      | ~ ( zip_tseitin_0 @ X5 @ X4 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('94',plain,
    ( ( k1_mcart_1 @ ( sk_B @ sk_A ) )
    = ( k4_tarski @ ( sk_E_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ sk_A @ sk_C_1 ) @ ( sk_F_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k1_mcart_1 @ ( sk_B @ sk_A ) )
    = ( k4_tarski @ ( sk_E_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ sk_A @ sk_C_1 ) @ ( sk_F_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('96',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X32 @ X33 ) )
      = X32 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('97',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) )
    = ( sk_E_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k1_mcart_1 @ ( sk_B @ sk_A ) )
    = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) ) @ ( sk_F_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['94','97'])).

thf('99',plain,(
    ! [X32: $i,X34: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X32 @ X34 ) )
      = X34 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('100',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) )
    = ( sk_F_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) ) @ sk_A ),
    inference(demod,[status(thm)],['91','100'])).

thf('102',plain,
    ( ( k1_mcart_1 @ ( sk_B @ sk_A ) )
    = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) ) @ ( sk_F_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['94','97'])).

thf('103',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) )
    = ( sk_F_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('104',plain,
    ( ( k1_mcart_1 @ ( sk_B @ sk_A ) )
    = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k3_mcart_1 @ X22 @ X23 @ X24 )
      = ( k4_tarski @ ( k4_tarski @ X22 @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) ) @ X0 )
      = ( k4_tarski @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( X28 = k1_xboole_0 )
      | ~ ( r2_hidden @ X29 @ X28 )
      | ( ( sk_B @ X28 )
       != ( k3_mcart_1 @ X30 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_B @ X1 )
       != ( k4_tarski @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ X0 ) )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( ( sk_B @ sk_A )
       != ( k4_tarski @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['101','108'])).

thf('110',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( sk_B @ sk_A )
     != ( k4_tarski @ ( k1_mcart_1 @ ( sk_B @ sk_A ) ) @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['109','110'])).

thf('112',plain,(
    ( sk_B @ sk_A )
 != ( sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['82','111'])).

thf('113',plain,(
    $false ),
    inference(simplify,[status(thm)],['112'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.25IoRDxKQj
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:39:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.82/1.04  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.82/1.04  % Solved by: fo/fo7.sh
% 0.82/1.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.82/1.04  % done 591 iterations in 0.585s
% 0.82/1.04  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.82/1.04  % SZS output start Refutation
% 0.82/1.04  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.82/1.04  thf(sk_A_type, type, sk_A: $i).
% 0.82/1.04  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.82/1.04  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.82/1.04  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.82/1.04  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.82/1.04  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.82/1.04  thf(sk_B_type, type, sk_B: $i > $i).
% 0.82/1.04  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.82/1.04  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.82/1.04  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i).
% 0.82/1.04  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.82/1.04  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.82/1.04  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.82/1.04  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.82/1.04  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.82/1.04  thf(t29_mcart_1, axiom,
% 0.82/1.04    (![A:$i]:
% 0.82/1.04     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.82/1.04          ( ![B:$i]:
% 0.82/1.04            ( ~( ( r2_hidden @ B @ A ) & 
% 0.82/1.04                 ( ![C:$i,D:$i,E:$i]:
% 0.82/1.04                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.82/1.04                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 0.82/1.04  thf('0', plain,
% 0.82/1.04      (![X28 : $i]:
% 0.82/1.04         (((X28) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X28) @ X28))),
% 0.82/1.04      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.82/1.04  thf(t49_mcart_1, conjecture,
% 0.82/1.04    (![A:$i,B:$i,C:$i]:
% 0.82/1.04     ( ( ~( ( ~( r1_tarski @ A @ ( k3_zfmisc_1 @ A @ B @ C ) ) ) & 
% 0.82/1.04            ( ~( r1_tarski @ A @ ( k3_zfmisc_1 @ B @ C @ A ) ) ) & 
% 0.82/1.04            ( ~( r1_tarski @ A @ ( k3_zfmisc_1 @ C @ A @ B ) ) ) ) ) =>
% 0.82/1.04       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.82/1.04  thf(zf_stmt_0, negated_conjecture,
% 0.82/1.04    (~( ![A:$i,B:$i,C:$i]:
% 0.82/1.04        ( ( ~( ( ~( r1_tarski @ A @ ( k3_zfmisc_1 @ A @ B @ C ) ) ) & 
% 0.82/1.04               ( ~( r1_tarski @ A @ ( k3_zfmisc_1 @ B @ C @ A ) ) ) & 
% 0.82/1.04               ( ~( r1_tarski @ A @ ( k3_zfmisc_1 @ C @ A @ B ) ) ) ) ) =>
% 0.82/1.04          ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.82/1.04    inference('cnf.neg', [status(esa)], [t49_mcart_1])).
% 0.82/1.04  thf('1', plain,
% 0.82/1.04      (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.82/1.04        | (r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_B_1 @ sk_C_1 @ sk_A))
% 0.82/1.04        | (r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_C_1 @ sk_A @ sk_B_1)))),
% 0.82/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.04  thf('2', plain,
% 0.82/1.04      (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_C_1 @ sk_A @ sk_B_1)))
% 0.82/1.04         <= (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_C_1 @ sk_A @ sk_B_1))))),
% 0.82/1.04      inference('split', [status(esa)], ['1'])).
% 0.82/1.04  thf(d3_tarski, axiom,
% 0.82/1.04    (![A:$i,B:$i]:
% 0.82/1.04     ( ( r1_tarski @ A @ B ) <=>
% 0.82/1.04       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.82/1.04  thf('3', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.04         (~ (r2_hidden @ X0 @ X1)
% 0.82/1.04          | (r2_hidden @ X0 @ X2)
% 0.82/1.04          | ~ (r1_tarski @ X1 @ X2))),
% 0.82/1.04      inference('cnf', [status(esa)], [d3_tarski])).
% 0.82/1.04  thf('4', plain,
% 0.82/1.04      ((![X0 : $i]:
% 0.82/1.04          ((r2_hidden @ X0 @ (k3_zfmisc_1 @ sk_C_1 @ sk_A @ sk_B_1))
% 0.82/1.04           | ~ (r2_hidden @ X0 @ sk_A)))
% 0.82/1.04         <= (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_C_1 @ sk_A @ sk_B_1))))),
% 0.82/1.04      inference('sup-', [status(thm)], ['2', '3'])).
% 0.82/1.04  thf('5', plain,
% 0.82/1.04      (((((sk_A) = (k1_xboole_0))
% 0.82/1.04         | (r2_hidden @ (sk_B @ sk_A) @ (k3_zfmisc_1 @ sk_C_1 @ sk_A @ sk_B_1))))
% 0.82/1.04         <= (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_C_1 @ sk_A @ sk_B_1))))),
% 0.82/1.04      inference('sup-', [status(thm)], ['0', '4'])).
% 0.82/1.04  thf('6', plain, (((sk_A) != (k1_xboole_0))),
% 0.82/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.04  thf('7', plain,
% 0.82/1.04      (((r2_hidden @ (sk_B @ sk_A) @ (k3_zfmisc_1 @ sk_C_1 @ sk_A @ sk_B_1)))
% 0.82/1.04         <= (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_C_1 @ sk_A @ sk_B_1))))),
% 0.82/1.04      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.82/1.04  thf('8', plain,
% 0.82/1.04      (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_B_1 @ sk_C_1 @ sk_A)))
% 0.82/1.04         <= (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_B_1 @ sk_C_1 @ sk_A))))),
% 0.82/1.04      inference('split', [status(esa)], ['1'])).
% 0.82/1.04  thf(d3_zfmisc_1, axiom,
% 0.82/1.04    (![A:$i,B:$i,C:$i]:
% 0.82/1.04     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.82/1.04       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.82/1.04  thf('9', plain,
% 0.82/1.04      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.82/1.04         ((k3_zfmisc_1 @ X25 @ X26 @ X27)
% 0.82/1.04           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26) @ X27))),
% 0.82/1.04      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.82/1.04  thf(t135_zfmisc_1, axiom,
% 0.82/1.04    (![A:$i,B:$i]:
% 0.82/1.04     ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) ) | 
% 0.82/1.04         ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.82/1.04       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.82/1.04  thf('10', plain,
% 0.82/1.04      (![X20 : $i, X21 : $i]:
% 0.82/1.04         (((X20) = (k1_xboole_0))
% 0.82/1.04          | ~ (r1_tarski @ X20 @ (k2_zfmisc_1 @ X21 @ X20)))),
% 0.82/1.04      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.82/1.04  thf('11', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.04         (~ (r1_tarski @ X0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.82/1.04          | ((X0) = (k1_xboole_0)))),
% 0.82/1.04      inference('sup-', [status(thm)], ['9', '10'])).
% 0.82/1.04  thf('12', plain,
% 0.82/1.04      ((((sk_A) = (k1_xboole_0)))
% 0.82/1.04         <= (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_B_1 @ sk_C_1 @ sk_A))))),
% 0.82/1.04      inference('sup-', [status(thm)], ['8', '11'])).
% 0.82/1.04  thf('13', plain, (((sk_A) != (k1_xboole_0))),
% 0.82/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.04  thf('14', plain,
% 0.82/1.04      (~ ((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_B_1 @ sk_C_1 @ sk_A)))),
% 0.82/1.04      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.82/1.04  thf('15', plain,
% 0.82/1.04      (![X28 : $i]:
% 0.82/1.04         (((X28) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X28) @ X28))),
% 0.82/1.04      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.82/1.04  thf('16', plain,
% 0.82/1.04      (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1)))
% 0.82/1.04         <= (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))))),
% 0.82/1.04      inference('split', [status(esa)], ['1'])).
% 0.82/1.04  thf('17', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.04         (~ (r2_hidden @ X0 @ X1)
% 0.82/1.04          | (r2_hidden @ X0 @ X2)
% 0.82/1.04          | ~ (r1_tarski @ X1 @ X2))),
% 0.82/1.04      inference('cnf', [status(esa)], [d3_tarski])).
% 0.82/1.04  thf('18', plain,
% 0.82/1.04      ((![X0 : $i]:
% 0.82/1.04          ((r2_hidden @ X0 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.82/1.04           | ~ (r2_hidden @ X0 @ sk_A)))
% 0.82/1.04         <= (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))))),
% 0.82/1.04      inference('sup-', [status(thm)], ['16', '17'])).
% 0.82/1.04  thf('19', plain,
% 0.82/1.04      (((((sk_A) = (k1_xboole_0))
% 0.82/1.04         | (r2_hidden @ (sk_B @ sk_A) @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))))
% 0.82/1.04         <= (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))))),
% 0.82/1.04      inference('sup-', [status(thm)], ['15', '18'])).
% 0.82/1.04  thf('20', plain, (((sk_A) != (k1_xboole_0))),
% 0.82/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.04  thf('21', plain,
% 0.82/1.04      (((r2_hidden @ (sk_B @ sk_A) @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1)))
% 0.82/1.04         <= (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))))),
% 0.82/1.04      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.82/1.04  thf('22', plain,
% 0.82/1.04      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.82/1.04         ((k3_zfmisc_1 @ X25 @ X26 @ X27)
% 0.82/1.04           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26) @ X27))),
% 0.82/1.04      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.82/1.04  thf(d2_zfmisc_1, axiom,
% 0.82/1.04    (![A:$i,B:$i,C:$i]:
% 0.82/1.04     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.82/1.04       ( ![D:$i]:
% 0.82/1.04         ( ( r2_hidden @ D @ C ) <=>
% 0.82/1.04           ( ?[E:$i,F:$i]:
% 0.82/1.04             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.82/1.04               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.82/1.04  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.82/1.04  thf(zf_stmt_2, axiom,
% 0.82/1.04    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.82/1.04     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.82/1.04       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.82/1.04         ( r2_hidden @ E @ A ) ) ))).
% 0.82/1.04  thf(zf_stmt_3, axiom,
% 0.82/1.04    (![A:$i,B:$i,C:$i]:
% 0.82/1.04     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.82/1.04       ( ![D:$i]:
% 0.82/1.04         ( ( r2_hidden @ D @ C ) <=>
% 0.82/1.04           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.82/1.04  thf('23', plain,
% 0.82/1.04      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.82/1.04         (~ (r2_hidden @ X16 @ X15)
% 0.82/1.04          | (zip_tseitin_0 @ (sk_F_1 @ X16 @ X13 @ X14) @ 
% 0.82/1.04             (sk_E_1 @ X16 @ X13 @ X14) @ X16 @ X13 @ X14)
% 0.82/1.04          | ((X15) != (k2_zfmisc_1 @ X14 @ X13)))),
% 0.82/1.04      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.82/1.04  thf('24', plain,
% 0.82/1.04      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.82/1.04         ((zip_tseitin_0 @ (sk_F_1 @ X16 @ X13 @ X14) @ 
% 0.82/1.04           (sk_E_1 @ X16 @ X13 @ X14) @ X16 @ X13 @ X14)
% 0.82/1.04          | ~ (r2_hidden @ X16 @ (k2_zfmisc_1 @ X14 @ X13)))),
% 0.82/1.04      inference('simplify', [status(thm)], ['23'])).
% 0.82/1.04  thf('25', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.82/1.04         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.82/1.04          | (zip_tseitin_0 @ (sk_F_1 @ X3 @ X0 @ (k2_zfmisc_1 @ X2 @ X1)) @ 
% 0.82/1.04             (sk_E_1 @ X3 @ X0 @ (k2_zfmisc_1 @ X2 @ X1)) @ X3 @ X0 @ 
% 0.82/1.04             (k2_zfmisc_1 @ X2 @ X1)))),
% 0.82/1.04      inference('sup-', [status(thm)], ['22', '24'])).
% 0.82/1.04  thf('26', plain,
% 0.82/1.04      (((zip_tseitin_0 @ 
% 0.82/1.04         (sk_F_1 @ (sk_B @ sk_A) @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) @ 
% 0.82/1.04         (sk_E_1 @ (sk_B @ sk_A) @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) @ 
% 0.82/1.04         (sk_B @ sk_A) @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 0.82/1.04         <= (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))))),
% 0.82/1.04      inference('sup-', [status(thm)], ['21', '25'])).
% 0.82/1.04  thf('27', plain,
% 0.82/1.04      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.82/1.04         (((X6) = (k4_tarski @ X4 @ X5))
% 0.82/1.04          | ~ (zip_tseitin_0 @ X5 @ X4 @ X6 @ X7 @ X8))),
% 0.82/1.04      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.82/1.04  thf('28', plain,
% 0.82/1.04      ((((sk_B @ sk_A)
% 0.82/1.04          = (k4_tarski @ 
% 0.82/1.04             (sk_E_1 @ (sk_B @ sk_A) @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) @ 
% 0.82/1.04             (sk_F_1 @ (sk_B @ sk_A) @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))))
% 0.82/1.04         <= (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))))),
% 0.82/1.04      inference('sup-', [status(thm)], ['26', '27'])).
% 0.82/1.04  thf('29', plain,
% 0.82/1.04      ((((sk_B @ sk_A)
% 0.82/1.04          = (k4_tarski @ 
% 0.82/1.04             (sk_E_1 @ (sk_B @ sk_A) @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) @ 
% 0.82/1.04             (sk_F_1 @ (sk_B @ sk_A) @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))))
% 0.82/1.04         <= (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))))),
% 0.82/1.04      inference('sup-', [status(thm)], ['26', '27'])).
% 0.82/1.04  thf(t7_mcart_1, axiom,
% 0.82/1.04    (![A:$i,B:$i]:
% 0.82/1.04     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.82/1.04       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.82/1.04  thf('30', plain,
% 0.82/1.04      (![X32 : $i, X33 : $i]: ((k1_mcart_1 @ (k4_tarski @ X32 @ X33)) = (X32))),
% 0.82/1.04      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.82/1.04  thf('31', plain,
% 0.82/1.04      ((((k1_mcart_1 @ (sk_B @ sk_A))
% 0.82/1.04          = (sk_E_1 @ (sk_B @ sk_A) @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))
% 0.82/1.04         <= (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))))),
% 0.82/1.04      inference('sup+', [status(thm)], ['29', '30'])).
% 0.82/1.04  thf('32', plain,
% 0.82/1.04      ((((sk_B @ sk_A)
% 0.82/1.04          = (k4_tarski @ (k1_mcart_1 @ (sk_B @ sk_A)) @ 
% 0.82/1.04             (sk_F_1 @ (sk_B @ sk_A) @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))))
% 0.82/1.04         <= (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))))),
% 0.82/1.04      inference('demod', [status(thm)], ['28', '31'])).
% 0.82/1.04  thf('33', plain,
% 0.82/1.04      ((((sk_B @ sk_A)
% 0.82/1.04          = (k4_tarski @ (k1_mcart_1 @ (sk_B @ sk_A)) @ 
% 0.82/1.04             (sk_F_1 @ (sk_B @ sk_A) @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))))
% 0.82/1.04         <= (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))))),
% 0.82/1.04      inference('demod', [status(thm)], ['28', '31'])).
% 0.82/1.04  thf('34', plain,
% 0.82/1.04      (![X32 : $i, X34 : $i]: ((k2_mcart_1 @ (k4_tarski @ X32 @ X34)) = (X34))),
% 0.82/1.04      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.82/1.04  thf('35', plain,
% 0.82/1.04      ((((k2_mcart_1 @ (sk_B @ sk_A))
% 0.82/1.04          = (sk_F_1 @ (sk_B @ sk_A) @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))
% 0.82/1.04         <= (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))))),
% 0.82/1.04      inference('sup+', [status(thm)], ['33', '34'])).
% 0.82/1.04  thf('36', plain,
% 0.82/1.04      ((((sk_B @ sk_A)
% 0.82/1.04          = (k4_tarski @ (k1_mcart_1 @ (sk_B @ sk_A)) @ 
% 0.82/1.04             (k2_mcart_1 @ (sk_B @ sk_A)))))
% 0.82/1.04         <= (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))))),
% 0.82/1.04      inference('demod', [status(thm)], ['32', '35'])).
% 0.82/1.04  thf('37', plain,
% 0.82/1.04      (((zip_tseitin_0 @ 
% 0.82/1.04         (sk_F_1 @ (sk_B @ sk_A) @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) @ 
% 0.82/1.04         (sk_E_1 @ (sk_B @ sk_A) @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) @ 
% 0.82/1.04         (sk_B @ sk_A) @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 0.82/1.04         <= (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))))),
% 0.82/1.04      inference('sup-', [status(thm)], ['21', '25'])).
% 0.82/1.04  thf('38', plain,
% 0.82/1.04      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.82/1.04         ((r2_hidden @ X4 @ X8) | ~ (zip_tseitin_0 @ X5 @ X4 @ X6 @ X7 @ X8))),
% 0.82/1.04      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.82/1.04  thf('39', plain,
% 0.82/1.04      (((r2_hidden @ 
% 0.82/1.04         (sk_E_1 @ (sk_B @ sk_A) @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) @ 
% 0.82/1.04         (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 0.82/1.04         <= (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))))),
% 0.82/1.04      inference('sup-', [status(thm)], ['37', '38'])).
% 0.82/1.04  thf('40', plain,
% 0.82/1.04      ((((k1_mcart_1 @ (sk_B @ sk_A))
% 0.82/1.04          = (sk_E_1 @ (sk_B @ sk_A) @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))
% 0.82/1.04         <= (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))))),
% 0.82/1.04      inference('sup+', [status(thm)], ['29', '30'])).
% 0.82/1.04  thf('41', plain,
% 0.82/1.04      (((r2_hidden @ (k1_mcart_1 @ (sk_B @ sk_A)) @ 
% 0.82/1.04         (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 0.82/1.04         <= (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))))),
% 0.82/1.04      inference('demod', [status(thm)], ['39', '40'])).
% 0.82/1.04  thf('42', plain,
% 0.82/1.04      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.82/1.04         ((zip_tseitin_0 @ (sk_F_1 @ X16 @ X13 @ X14) @ 
% 0.82/1.04           (sk_E_1 @ X16 @ X13 @ X14) @ X16 @ X13 @ X14)
% 0.82/1.04          | ~ (r2_hidden @ X16 @ (k2_zfmisc_1 @ X14 @ X13)))),
% 0.82/1.04      inference('simplify', [status(thm)], ['23'])).
% 0.82/1.04  thf('43', plain,
% 0.82/1.04      (((zip_tseitin_0 @ 
% 0.82/1.04         (sk_F_1 @ (k1_mcart_1 @ (sk_B @ sk_A)) @ sk_B_1 @ sk_A) @ 
% 0.82/1.04         (sk_E_1 @ (k1_mcart_1 @ (sk_B @ sk_A)) @ sk_B_1 @ sk_A) @ 
% 0.82/1.04         (k1_mcart_1 @ (sk_B @ sk_A)) @ sk_B_1 @ sk_A))
% 0.82/1.04         <= (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))))),
% 0.82/1.04      inference('sup-', [status(thm)], ['41', '42'])).
% 0.82/1.04  thf('44', plain,
% 0.82/1.04      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.82/1.04         ((r2_hidden @ X4 @ X8) | ~ (zip_tseitin_0 @ X5 @ X4 @ X6 @ X7 @ X8))),
% 0.82/1.04      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.82/1.04  thf('45', plain,
% 0.82/1.04      (((r2_hidden @ (sk_E_1 @ (k1_mcart_1 @ (sk_B @ sk_A)) @ sk_B_1 @ sk_A) @ 
% 0.82/1.04         sk_A))
% 0.82/1.04         <= (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))))),
% 0.82/1.04      inference('sup-', [status(thm)], ['43', '44'])).
% 0.82/1.04  thf('46', plain,
% 0.82/1.04      (((zip_tseitin_0 @ 
% 0.82/1.04         (sk_F_1 @ (k1_mcart_1 @ (sk_B @ sk_A)) @ sk_B_1 @ sk_A) @ 
% 0.82/1.04         (sk_E_1 @ (k1_mcart_1 @ (sk_B @ sk_A)) @ sk_B_1 @ sk_A) @ 
% 0.82/1.04         (k1_mcart_1 @ (sk_B @ sk_A)) @ sk_B_1 @ sk_A))
% 0.82/1.04         <= (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))))),
% 0.82/1.04      inference('sup-', [status(thm)], ['41', '42'])).
% 0.82/1.04  thf('47', plain,
% 0.82/1.04      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.82/1.04         (((X6) = (k4_tarski @ X4 @ X5))
% 0.82/1.04          | ~ (zip_tseitin_0 @ X5 @ X4 @ X6 @ X7 @ X8))),
% 0.82/1.04      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.82/1.04  thf('48', plain,
% 0.82/1.04      ((((k1_mcart_1 @ (sk_B @ sk_A))
% 0.82/1.04          = (k4_tarski @ 
% 0.82/1.04             (sk_E_1 @ (k1_mcart_1 @ (sk_B @ sk_A)) @ sk_B_1 @ sk_A) @ 
% 0.82/1.04             (sk_F_1 @ (k1_mcart_1 @ (sk_B @ sk_A)) @ sk_B_1 @ sk_A))))
% 0.82/1.04         <= (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))))),
% 0.82/1.04      inference('sup-', [status(thm)], ['46', '47'])).
% 0.82/1.04  thf('49', plain,
% 0.82/1.04      (![X32 : $i, X33 : $i]: ((k1_mcart_1 @ (k4_tarski @ X32 @ X33)) = (X32))),
% 0.82/1.04      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.82/1.04  thf('50', plain,
% 0.82/1.04      ((((k1_mcart_1 @ (k1_mcart_1 @ (sk_B @ sk_A)))
% 0.82/1.04          = (sk_E_1 @ (k1_mcart_1 @ (sk_B @ sk_A)) @ sk_B_1 @ sk_A)))
% 0.82/1.04         <= (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))))),
% 0.82/1.04      inference('sup+', [status(thm)], ['48', '49'])).
% 0.82/1.04  thf('51', plain,
% 0.82/1.04      (((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ (sk_B @ sk_A))) @ sk_A))
% 0.82/1.04         <= (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))))),
% 0.82/1.04      inference('demod', [status(thm)], ['45', '50'])).
% 0.82/1.04  thf('52', plain,
% 0.82/1.04      ((((k1_mcart_1 @ (sk_B @ sk_A))
% 0.82/1.04          = (k4_tarski @ 
% 0.82/1.04             (sk_E_1 @ (k1_mcart_1 @ (sk_B @ sk_A)) @ sk_B_1 @ sk_A) @ 
% 0.82/1.04             (sk_F_1 @ (k1_mcart_1 @ (sk_B @ sk_A)) @ sk_B_1 @ sk_A))))
% 0.82/1.04         <= (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))))),
% 0.82/1.04      inference('sup-', [status(thm)], ['46', '47'])).
% 0.82/1.04  thf('53', plain,
% 0.82/1.04      ((((k1_mcart_1 @ (k1_mcart_1 @ (sk_B @ sk_A)))
% 0.82/1.04          = (sk_E_1 @ (k1_mcart_1 @ (sk_B @ sk_A)) @ sk_B_1 @ sk_A)))
% 0.82/1.04         <= (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))))),
% 0.82/1.04      inference('sup+', [status(thm)], ['48', '49'])).
% 0.82/1.04  thf('54', plain,
% 0.82/1.04      ((((k1_mcart_1 @ (sk_B @ sk_A))
% 0.82/1.04          = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ (sk_B @ sk_A))) @ 
% 0.82/1.04             (sk_F_1 @ (k1_mcart_1 @ (sk_B @ sk_A)) @ sk_B_1 @ sk_A))))
% 0.82/1.04         <= (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))))),
% 0.82/1.04      inference('demod', [status(thm)], ['52', '53'])).
% 0.82/1.04  thf('55', plain,
% 0.82/1.04      ((((k1_mcart_1 @ (sk_B @ sk_A))
% 0.82/1.04          = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ (sk_B @ sk_A))) @ 
% 0.82/1.04             (sk_F_1 @ (k1_mcart_1 @ (sk_B @ sk_A)) @ sk_B_1 @ sk_A))))
% 0.82/1.04         <= (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))))),
% 0.82/1.04      inference('demod', [status(thm)], ['52', '53'])).
% 0.82/1.04  thf('56', plain,
% 0.82/1.04      (![X32 : $i, X34 : $i]: ((k2_mcart_1 @ (k4_tarski @ X32 @ X34)) = (X34))),
% 0.82/1.04      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.82/1.04  thf('57', plain,
% 0.82/1.04      ((((k2_mcart_1 @ (k1_mcart_1 @ (sk_B @ sk_A)))
% 0.82/1.04          = (sk_F_1 @ (k1_mcart_1 @ (sk_B @ sk_A)) @ sk_B_1 @ sk_A)))
% 0.82/1.04         <= (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))))),
% 0.82/1.04      inference('sup+', [status(thm)], ['55', '56'])).
% 0.82/1.04  thf('58', plain,
% 0.82/1.04      ((((k1_mcart_1 @ (sk_B @ sk_A))
% 0.82/1.04          = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ (sk_B @ sk_A))) @ 
% 0.82/1.04             (k2_mcart_1 @ (k1_mcart_1 @ (sk_B @ sk_A))))))
% 0.82/1.04         <= (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))))),
% 0.82/1.04      inference('demod', [status(thm)], ['54', '57'])).
% 0.82/1.04  thf(d3_mcart_1, axiom,
% 0.82/1.04    (![A:$i,B:$i,C:$i]:
% 0.82/1.04     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.82/1.04  thf('59', plain,
% 0.82/1.04      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.82/1.04         ((k3_mcart_1 @ X22 @ X23 @ X24)
% 0.82/1.04           = (k4_tarski @ (k4_tarski @ X22 @ X23) @ X24))),
% 0.82/1.04      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.82/1.04  thf('60', plain,
% 0.82/1.04      ((![X0 : $i]:
% 0.82/1.04          ((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ (sk_B @ sk_A))) @ 
% 0.82/1.04            (k2_mcart_1 @ (k1_mcart_1 @ (sk_B @ sk_A))) @ X0)
% 0.82/1.04            = (k4_tarski @ (k1_mcart_1 @ (sk_B @ sk_A)) @ X0)))
% 0.82/1.04         <= (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))))),
% 0.82/1.04      inference('sup+', [status(thm)], ['58', '59'])).
% 0.82/1.04  thf('61', plain,
% 0.82/1.04      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.82/1.04         (((X28) = (k1_xboole_0))
% 0.82/1.04          | ~ (r2_hidden @ X30 @ X28)
% 0.82/1.04          | ((sk_B @ X28) != (k3_mcart_1 @ X30 @ X29 @ X31)))),
% 0.82/1.04      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.82/1.04  thf('62', plain,
% 0.82/1.04      ((![X0 : $i, X1 : $i]:
% 0.82/1.04          (((sk_B @ X1) != (k4_tarski @ (k1_mcart_1 @ (sk_B @ sk_A)) @ X0))
% 0.82/1.04           | ~ (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ (sk_B @ sk_A))) @ X1)
% 0.82/1.04           | ((X1) = (k1_xboole_0))))
% 0.82/1.04         <= (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))))),
% 0.82/1.04      inference('sup-', [status(thm)], ['60', '61'])).
% 0.82/1.04  thf('63', plain,
% 0.82/1.04      ((![X0 : $i]:
% 0.82/1.04          (((sk_A) = (k1_xboole_0))
% 0.82/1.04           | ((sk_B @ sk_A) != (k4_tarski @ (k1_mcart_1 @ (sk_B @ sk_A)) @ X0))))
% 0.82/1.04         <= (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))))),
% 0.82/1.04      inference('sup-', [status(thm)], ['51', '62'])).
% 0.82/1.04  thf('64', plain, (((sk_A) != (k1_xboole_0))),
% 0.82/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.04  thf('65', plain,
% 0.82/1.04      ((![X0 : $i]:
% 0.82/1.04          ((sk_B @ sk_A) != (k4_tarski @ (k1_mcart_1 @ (sk_B @ sk_A)) @ X0)))
% 0.82/1.04         <= (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))))),
% 0.82/1.04      inference('simplify_reflect-', [status(thm)], ['63', '64'])).
% 0.82/1.04  thf('66', plain,
% 0.82/1.04      ((((sk_B @ sk_A) != (sk_B @ sk_A)))
% 0.82/1.04         <= (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))))),
% 0.82/1.04      inference('sup-', [status(thm)], ['36', '65'])).
% 0.82/1.04  thf('67', plain,
% 0.82/1.04      (~ ((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.82/1.04      inference('simplify', [status(thm)], ['66'])).
% 0.82/1.04  thf('68', plain,
% 0.82/1.04      (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_C_1 @ sk_A @ sk_B_1))) | 
% 0.82/1.04       ((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))) | 
% 0.82/1.04       ((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_B_1 @ sk_C_1 @ sk_A)))),
% 0.82/1.04      inference('split', [status(esa)], ['1'])).
% 0.82/1.04  thf('69', plain,
% 0.82/1.04      (((r1_tarski @ sk_A @ (k3_zfmisc_1 @ sk_C_1 @ sk_A @ sk_B_1)))),
% 0.82/1.04      inference('sat_resolution*', [status(thm)], ['14', '67', '68'])).
% 0.82/1.04  thf('70', plain,
% 0.82/1.04      ((r2_hidden @ (sk_B @ sk_A) @ (k3_zfmisc_1 @ sk_C_1 @ sk_A @ sk_B_1))),
% 0.82/1.04      inference('simpl_trail', [status(thm)], ['7', '69'])).
% 0.82/1.04  thf('71', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.82/1.04         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.82/1.04          | (zip_tseitin_0 @ (sk_F_1 @ X3 @ X0 @ (k2_zfmisc_1 @ X2 @ X1)) @ 
% 0.82/1.04             (sk_E_1 @ X3 @ X0 @ (k2_zfmisc_1 @ X2 @ X1)) @ X3 @ X0 @ 
% 0.82/1.04             (k2_zfmisc_1 @ X2 @ X1)))),
% 0.82/1.04      inference('sup-', [status(thm)], ['22', '24'])).
% 0.82/1.04  thf('72', plain,
% 0.82/1.04      ((zip_tseitin_0 @ 
% 0.82/1.04        (sk_F_1 @ (sk_B @ sk_A) @ sk_B_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)) @ 
% 0.82/1.04        (sk_E_1 @ (sk_B @ sk_A) @ sk_B_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)) @ 
% 0.82/1.04        (sk_B @ sk_A) @ sk_B_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A))),
% 0.82/1.04      inference('sup-', [status(thm)], ['70', '71'])).
% 0.82/1.04  thf('73', plain,
% 0.82/1.04      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.82/1.04         (((X6) = (k4_tarski @ X4 @ X5))
% 0.82/1.04          | ~ (zip_tseitin_0 @ X5 @ X4 @ X6 @ X7 @ X8))),
% 0.82/1.04      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.82/1.04  thf('74', plain,
% 0.82/1.04      (((sk_B @ sk_A)
% 0.82/1.04         = (k4_tarski @ 
% 0.82/1.04            (sk_E_1 @ (sk_B @ sk_A) @ sk_B_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)) @ 
% 0.82/1.04            (sk_F_1 @ (sk_B @ sk_A) @ sk_B_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A))))),
% 0.82/1.04      inference('sup-', [status(thm)], ['72', '73'])).
% 0.82/1.04  thf('75', plain,
% 0.82/1.04      (((sk_B @ sk_A)
% 0.82/1.04         = (k4_tarski @ 
% 0.82/1.04            (sk_E_1 @ (sk_B @ sk_A) @ sk_B_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)) @ 
% 0.82/1.04            (sk_F_1 @ (sk_B @ sk_A) @ sk_B_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A))))),
% 0.82/1.04      inference('sup-', [status(thm)], ['72', '73'])).
% 0.82/1.04  thf('76', plain,
% 0.82/1.04      (![X32 : $i, X33 : $i]: ((k1_mcart_1 @ (k4_tarski @ X32 @ X33)) = (X32))),
% 0.82/1.04      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.82/1.04  thf('77', plain,
% 0.82/1.04      (((k1_mcart_1 @ (sk_B @ sk_A))
% 0.82/1.04         = (sk_E_1 @ (sk_B @ sk_A) @ sk_B_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.82/1.04      inference('sup+', [status(thm)], ['75', '76'])).
% 0.82/1.04  thf('78', plain,
% 0.82/1.04      (((sk_B @ sk_A)
% 0.82/1.04         = (k4_tarski @ (k1_mcart_1 @ (sk_B @ sk_A)) @ 
% 0.82/1.04            (sk_F_1 @ (sk_B @ sk_A) @ sk_B_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A))))),
% 0.82/1.04      inference('demod', [status(thm)], ['74', '77'])).
% 0.82/1.04  thf('79', plain,
% 0.82/1.04      (((sk_B @ sk_A)
% 0.82/1.04         = (k4_tarski @ (k1_mcart_1 @ (sk_B @ sk_A)) @ 
% 0.82/1.04            (sk_F_1 @ (sk_B @ sk_A) @ sk_B_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A))))),
% 0.82/1.04      inference('demod', [status(thm)], ['74', '77'])).
% 0.82/1.04  thf('80', plain,
% 0.82/1.04      (![X32 : $i, X34 : $i]: ((k2_mcart_1 @ (k4_tarski @ X32 @ X34)) = (X34))),
% 0.82/1.04      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.82/1.04  thf('81', plain,
% 0.82/1.04      (((k2_mcart_1 @ (sk_B @ sk_A))
% 0.82/1.04         = (sk_F_1 @ (sk_B @ sk_A) @ sk_B_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.82/1.04      inference('sup+', [status(thm)], ['79', '80'])).
% 0.82/1.04  thf('82', plain,
% 0.82/1.04      (((sk_B @ sk_A)
% 0.82/1.04         = (k4_tarski @ (k1_mcart_1 @ (sk_B @ sk_A)) @ 
% 0.82/1.04            (k2_mcart_1 @ (sk_B @ sk_A))))),
% 0.82/1.04      inference('demod', [status(thm)], ['78', '81'])).
% 0.82/1.04  thf('83', plain,
% 0.82/1.04      ((zip_tseitin_0 @ 
% 0.82/1.04        (sk_F_1 @ (sk_B @ sk_A) @ sk_B_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)) @ 
% 0.82/1.04        (sk_E_1 @ (sk_B @ sk_A) @ sk_B_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)) @ 
% 0.82/1.04        (sk_B @ sk_A) @ sk_B_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A))),
% 0.82/1.04      inference('sup-', [status(thm)], ['70', '71'])).
% 0.82/1.04  thf('84', plain,
% 0.82/1.04      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.82/1.04         ((r2_hidden @ X4 @ X8) | ~ (zip_tseitin_0 @ X5 @ X4 @ X6 @ X7 @ X8))),
% 0.82/1.04      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.82/1.04  thf('85', plain,
% 0.82/1.04      ((r2_hidden @ 
% 0.82/1.04        (sk_E_1 @ (sk_B @ sk_A) @ sk_B_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)) @ 
% 0.82/1.04        (k2_zfmisc_1 @ sk_C_1 @ sk_A))),
% 0.82/1.04      inference('sup-', [status(thm)], ['83', '84'])).
% 0.82/1.04  thf('86', plain,
% 0.82/1.04      (((k1_mcart_1 @ (sk_B @ sk_A))
% 0.82/1.04         = (sk_E_1 @ (sk_B @ sk_A) @ sk_B_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.82/1.04      inference('sup+', [status(thm)], ['75', '76'])).
% 0.82/1.04  thf('87', plain,
% 0.82/1.04      ((r2_hidden @ (k1_mcart_1 @ (sk_B @ sk_A)) @ 
% 0.82/1.04        (k2_zfmisc_1 @ sk_C_1 @ sk_A))),
% 0.82/1.04      inference('demod', [status(thm)], ['85', '86'])).
% 0.82/1.04  thf('88', plain,
% 0.82/1.04      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.82/1.04         ((zip_tseitin_0 @ (sk_F_1 @ X16 @ X13 @ X14) @ 
% 0.82/1.04           (sk_E_1 @ X16 @ X13 @ X14) @ X16 @ X13 @ X14)
% 0.82/1.04          | ~ (r2_hidden @ X16 @ (k2_zfmisc_1 @ X14 @ X13)))),
% 0.82/1.04      inference('simplify', [status(thm)], ['23'])).
% 0.82/1.04  thf('89', plain,
% 0.82/1.04      ((zip_tseitin_0 @ 
% 0.82/1.04        (sk_F_1 @ (k1_mcart_1 @ (sk_B @ sk_A)) @ sk_A @ sk_C_1) @ 
% 0.82/1.04        (sk_E_1 @ (k1_mcart_1 @ (sk_B @ sk_A)) @ sk_A @ sk_C_1) @ 
% 0.82/1.04        (k1_mcart_1 @ (sk_B @ sk_A)) @ sk_A @ sk_C_1)),
% 0.82/1.04      inference('sup-', [status(thm)], ['87', '88'])).
% 0.82/1.04  thf('90', plain,
% 0.82/1.04      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.82/1.04         ((r2_hidden @ X5 @ X7) | ~ (zip_tseitin_0 @ X5 @ X4 @ X6 @ X7 @ X8))),
% 0.82/1.04      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.82/1.04  thf('91', plain,
% 0.82/1.04      ((r2_hidden @ (sk_F_1 @ (k1_mcart_1 @ (sk_B @ sk_A)) @ sk_A @ sk_C_1) @ 
% 0.82/1.04        sk_A)),
% 0.82/1.04      inference('sup-', [status(thm)], ['89', '90'])).
% 0.82/1.04  thf('92', plain,
% 0.82/1.04      ((zip_tseitin_0 @ 
% 0.82/1.04        (sk_F_1 @ (k1_mcart_1 @ (sk_B @ sk_A)) @ sk_A @ sk_C_1) @ 
% 0.82/1.04        (sk_E_1 @ (k1_mcart_1 @ (sk_B @ sk_A)) @ sk_A @ sk_C_1) @ 
% 0.82/1.04        (k1_mcart_1 @ (sk_B @ sk_A)) @ sk_A @ sk_C_1)),
% 0.82/1.04      inference('sup-', [status(thm)], ['87', '88'])).
% 0.82/1.04  thf('93', plain,
% 0.82/1.04      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.82/1.04         (((X6) = (k4_tarski @ X4 @ X5))
% 0.82/1.04          | ~ (zip_tseitin_0 @ X5 @ X4 @ X6 @ X7 @ X8))),
% 0.82/1.04      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.82/1.04  thf('94', plain,
% 0.82/1.04      (((k1_mcart_1 @ (sk_B @ sk_A))
% 0.82/1.04         = (k4_tarski @ 
% 0.82/1.04            (sk_E_1 @ (k1_mcart_1 @ (sk_B @ sk_A)) @ sk_A @ sk_C_1) @ 
% 0.82/1.04            (sk_F_1 @ (k1_mcart_1 @ (sk_B @ sk_A)) @ sk_A @ sk_C_1)))),
% 0.82/1.04      inference('sup-', [status(thm)], ['92', '93'])).
% 0.82/1.04  thf('95', plain,
% 0.82/1.04      (((k1_mcart_1 @ (sk_B @ sk_A))
% 0.82/1.04         = (k4_tarski @ 
% 0.82/1.04            (sk_E_1 @ (k1_mcart_1 @ (sk_B @ sk_A)) @ sk_A @ sk_C_1) @ 
% 0.82/1.04            (sk_F_1 @ (k1_mcart_1 @ (sk_B @ sk_A)) @ sk_A @ sk_C_1)))),
% 0.82/1.04      inference('sup-', [status(thm)], ['92', '93'])).
% 0.82/1.04  thf('96', plain,
% 0.82/1.04      (![X32 : $i, X33 : $i]: ((k1_mcart_1 @ (k4_tarski @ X32 @ X33)) = (X32))),
% 0.82/1.04      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.82/1.04  thf('97', plain,
% 0.82/1.04      (((k1_mcart_1 @ (k1_mcart_1 @ (sk_B @ sk_A)))
% 0.82/1.04         = (sk_E_1 @ (k1_mcart_1 @ (sk_B @ sk_A)) @ sk_A @ sk_C_1))),
% 0.82/1.04      inference('sup+', [status(thm)], ['95', '96'])).
% 0.82/1.04  thf('98', plain,
% 0.82/1.04      (((k1_mcart_1 @ (sk_B @ sk_A))
% 0.82/1.04         = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ (sk_B @ sk_A))) @ 
% 0.82/1.04            (sk_F_1 @ (k1_mcart_1 @ (sk_B @ sk_A)) @ sk_A @ sk_C_1)))),
% 0.82/1.04      inference('demod', [status(thm)], ['94', '97'])).
% 0.82/1.04  thf('99', plain,
% 0.82/1.04      (![X32 : $i, X34 : $i]: ((k2_mcart_1 @ (k4_tarski @ X32 @ X34)) = (X34))),
% 0.82/1.04      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.82/1.04  thf('100', plain,
% 0.82/1.04      (((k2_mcart_1 @ (k1_mcart_1 @ (sk_B @ sk_A)))
% 0.82/1.04         = (sk_F_1 @ (k1_mcart_1 @ (sk_B @ sk_A)) @ sk_A @ sk_C_1))),
% 0.82/1.04      inference('sup+', [status(thm)], ['98', '99'])).
% 0.82/1.04  thf('101', plain,
% 0.82/1.04      ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ (sk_B @ sk_A))) @ sk_A)),
% 0.82/1.04      inference('demod', [status(thm)], ['91', '100'])).
% 0.82/1.04  thf('102', plain,
% 0.82/1.04      (((k1_mcart_1 @ (sk_B @ sk_A))
% 0.82/1.04         = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ (sk_B @ sk_A))) @ 
% 0.82/1.04            (sk_F_1 @ (k1_mcart_1 @ (sk_B @ sk_A)) @ sk_A @ sk_C_1)))),
% 0.82/1.04      inference('demod', [status(thm)], ['94', '97'])).
% 0.82/1.04  thf('103', plain,
% 0.82/1.04      (((k2_mcart_1 @ (k1_mcart_1 @ (sk_B @ sk_A)))
% 0.82/1.04         = (sk_F_1 @ (k1_mcart_1 @ (sk_B @ sk_A)) @ sk_A @ sk_C_1))),
% 0.82/1.04      inference('sup+', [status(thm)], ['98', '99'])).
% 0.82/1.04  thf('104', plain,
% 0.82/1.04      (((k1_mcart_1 @ (sk_B @ sk_A))
% 0.82/1.04         = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ (sk_B @ sk_A))) @ 
% 0.82/1.04            (k2_mcart_1 @ (k1_mcart_1 @ (sk_B @ sk_A)))))),
% 0.82/1.04      inference('demod', [status(thm)], ['102', '103'])).
% 0.82/1.04  thf('105', plain,
% 0.82/1.04      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.82/1.04         ((k3_mcart_1 @ X22 @ X23 @ X24)
% 0.82/1.04           = (k4_tarski @ (k4_tarski @ X22 @ X23) @ X24))),
% 0.82/1.04      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.82/1.04  thf('106', plain,
% 0.82/1.04      (![X0 : $i]:
% 0.82/1.04         ((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ (sk_B @ sk_A))) @ 
% 0.82/1.04           (k2_mcart_1 @ (k1_mcart_1 @ (sk_B @ sk_A))) @ X0)
% 0.82/1.04           = (k4_tarski @ (k1_mcart_1 @ (sk_B @ sk_A)) @ X0))),
% 0.82/1.04      inference('sup+', [status(thm)], ['104', '105'])).
% 0.82/1.04  thf('107', plain,
% 0.82/1.04      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.82/1.04         (((X28) = (k1_xboole_0))
% 0.82/1.04          | ~ (r2_hidden @ X29 @ X28)
% 0.82/1.04          | ((sk_B @ X28) != (k3_mcart_1 @ X30 @ X29 @ X31)))),
% 0.82/1.04      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.82/1.04  thf('108', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i]:
% 0.82/1.04         (((sk_B @ X1) != (k4_tarski @ (k1_mcart_1 @ (sk_B @ sk_A)) @ X0))
% 0.82/1.04          | ~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ (sk_B @ sk_A))) @ X1)
% 0.82/1.04          | ((X1) = (k1_xboole_0)))),
% 0.82/1.04      inference('sup-', [status(thm)], ['106', '107'])).
% 0.82/1.04  thf('109', plain,
% 0.82/1.04      (![X0 : $i]:
% 0.82/1.04         (((sk_A) = (k1_xboole_0))
% 0.82/1.04          | ((sk_B @ sk_A) != (k4_tarski @ (k1_mcart_1 @ (sk_B @ sk_A)) @ X0)))),
% 0.82/1.04      inference('sup-', [status(thm)], ['101', '108'])).
% 0.82/1.04  thf('110', plain, (((sk_A) != (k1_xboole_0))),
% 0.82/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.04  thf('111', plain,
% 0.82/1.04      (![X0 : $i]:
% 0.82/1.04         ((sk_B @ sk_A) != (k4_tarski @ (k1_mcart_1 @ (sk_B @ sk_A)) @ X0))),
% 0.82/1.04      inference('simplify_reflect-', [status(thm)], ['109', '110'])).
% 0.82/1.04  thf('112', plain, (((sk_B @ sk_A) != (sk_B @ sk_A))),
% 0.82/1.04      inference('sup-', [status(thm)], ['82', '111'])).
% 0.82/1.04  thf('113', plain, ($false), inference('simplify', [status(thm)], ['112'])).
% 0.82/1.04  
% 0.82/1.04  % SZS output end Refutation
% 0.82/1.04  
% 0.82/1.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
