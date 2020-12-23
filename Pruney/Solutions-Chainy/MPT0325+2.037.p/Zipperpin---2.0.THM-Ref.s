%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EfA0D84iZb

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:45 EST 2020

% Result     : Theorem 0.57s
% Output     : Refutation 0.57s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 224 expanded)
%              Number of leaves         :   30 (  80 expanded)
%              Depth                    :   15
%              Number of atoms          : 1090 (2270 expanded)
%              Number of equality atoms :   59 ( 125 expanded)
%              Maximal formula depth    :   16 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('2',plain,(
    ! [X32: $i,X33: $i,X34: $i,X36: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X32 @ X34 ) @ ( k2_zfmisc_1 @ X33 @ X36 ) )
      | ~ ( r2_hidden @ X34 @ X36 )
      | ~ ( r2_hidden @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_C @ X2 @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r1_tarski @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t138_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
     => ( ( ( k2_zfmisc_1 @ A @ B )
          = k1_xboole_0 )
        | ( ( r1_tarski @ A @ C )
          & ( r1_tarski @ B @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
       => ( ( ( k2_zfmisc_1 @ A @ B )
            = k1_xboole_0 )
          | ( ( r1_tarski @ A @ C )
            & ( r1_tarski @ B @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t138_zfmisc_1])).

thf('5',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_C @ X0 @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( r2_hidden @ X34 @ X35 )
      | ~ ( r2_hidden @ ( k4_tarski @ X32 @ X34 ) @ ( k2_zfmisc_1 @ X33 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_D_1 )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_B_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_B_1 @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_2 )
    | ~ ( r1_tarski @ sk_B_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_D_1 )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D_1 ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('18',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('20',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    r2_hidden @ ( sk_B @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ),
    inference('simplify_reflect-',[status(thm)],['20','21'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('23',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['17','24'])).

thf('26',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['16','27'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('29',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('30',plain,(
    ! [X13: $i,X15: $i] :
      ( ( r1_xboole_0 @ X13 @ X15 )
      | ( ( k4_xboole_0 @ X13 @ X15 )
       != X13 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( X0 != X0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['31'])).

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

thf('34',plain,(
    ! [X25: $i,X26: $i,X29: $i] :
      ( ( X29
        = ( k2_zfmisc_1 @ X26 @ X25 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X29 @ X25 @ X26 ) @ ( sk_E @ X29 @ X25 @ X26 ) @ ( sk_D @ X29 @ X25 @ X26 ) @ X25 @ X26 )
      | ( r2_hidden @ ( sk_D @ X29 @ X25 @ X26 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('35',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X17 @ X19 )
      | ~ ( zip_tseitin_0 @ X17 @ X16 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('38',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_F @ X0 @ X2 @ X1 ) @ X2 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_F @ X0 @ X2 @ X1 ) @ X2 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_F @ X0 @ X2 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_F @ X0 @ X2 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','41'])).

thf('44',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','47'])).

thf('49',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('50',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('51',plain,(
    ! [X32: $i,X33: $i,X34: $i,X36: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X32 @ X34 ) @ ( k2_zfmisc_1 @ X33 @ X36 ) )
      | ~ ( r2_hidden @ X34 @ X36 )
      | ~ ( r2_hidden @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_B @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_B @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 = k1_xboole_0 )
      | ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( r2_hidden @ X32 @ X33 )
      | ~ ( r2_hidden @ ( k4_tarski @ X32 @ X34 ) @ ( k2_zfmisc_1 @ X33 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('59',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_C_2 )
    | ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( r1_tarski @ sk_A @ sk_C_2 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_2 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference(split,[status(esa)],['14'])).

thf('62',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['48','64'])).

thf('66',plain,(
    r1_tarski @ sk_A @ sk_C_2 ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_D_1 )
    | ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference(split,[status(esa)],['14'])).

thf('68',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_D_1 ) ),
    inference('sat_resolution*',[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) ),
    inference(simpl_trail,[status(thm)],['28','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('71',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('73',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('74',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X28 @ X27 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X28 @ X25 @ X26 ) @ ( sk_E_1 @ X28 @ X25 @ X26 ) @ X28 @ X25 @ X26 )
      | ( X27
       != ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('75',plain,(
    ! [X25: $i,X26: $i,X28: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X28 @ X25 @ X26 ) @ ( sk_E_1 @ X28 @ X25 @ X26 ) @ X28 @ X25 @ X26 )
      | ~ ( r2_hidden @ X28 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_E_1 @ ( sk_C @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['73','75'])).

thf('77',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X16 @ X20 )
      | ~ ( zip_tseitin_0 @ X17 @ X16 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_C @ X2 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_C @ X2 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('80',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_xboole_0 @ X0 @ X3 )
      | ~ ( r2_hidden @ ( sk_E_1 @ ( sk_C @ X2 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['72','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['71','86'])).

thf('88',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('89',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) @ X0 )
      | ( ( k2_zfmisc_1 @ k1_xboole_0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['87','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) @ X0 )
      | ( ( k2_zfmisc_1 @ k1_xboole_0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('95',plain,(
    $false ),
    inference(demod,[status(thm)],['69','93','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EfA0D84iZb
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:20:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.57/0.81  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.57/0.81  % Solved by: fo/fo7.sh
% 0.57/0.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.57/0.81  % done 337 iterations in 0.338s
% 0.57/0.81  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.57/0.81  % SZS output start Refutation
% 0.57/0.81  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i).
% 0.57/0.81  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.57/0.81  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.57/0.81  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.57/0.81  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.57/0.81  thf(sk_B_type, type, sk_B: $i > $i).
% 0.57/0.81  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.57/0.81  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.57/0.81  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.57/0.81  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.57/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.57/0.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.57/0.81  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.57/0.81  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.57/0.81  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.57/0.81  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.57/0.81  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.57/0.81  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.57/0.81  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.57/0.81  thf(t7_xboole_0, axiom,
% 0.57/0.81    (![A:$i]:
% 0.57/0.81     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.57/0.81          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.57/0.81  thf('0', plain,
% 0.57/0.81      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.57/0.81      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.57/0.81  thf(d3_tarski, axiom,
% 0.57/0.81    (![A:$i,B:$i]:
% 0.57/0.81     ( ( r1_tarski @ A @ B ) <=>
% 0.57/0.81       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.57/0.81  thf('1', plain,
% 0.57/0.81      (![X1 : $i, X3 : $i]:
% 0.57/0.81         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.57/0.81      inference('cnf', [status(esa)], [d3_tarski])).
% 0.57/0.81  thf(l54_zfmisc_1, axiom,
% 0.57/0.81    (![A:$i,B:$i,C:$i,D:$i]:
% 0.57/0.81     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.57/0.81       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.57/0.81  thf('2', plain,
% 0.57/0.81      (![X32 : $i, X33 : $i, X34 : $i, X36 : $i]:
% 0.57/0.81         ((r2_hidden @ (k4_tarski @ X32 @ X34) @ (k2_zfmisc_1 @ X33 @ X36))
% 0.57/0.81          | ~ (r2_hidden @ X34 @ X36)
% 0.57/0.81          | ~ (r2_hidden @ X32 @ X33))),
% 0.57/0.81      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.57/0.81  thf('3', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.57/0.81         ((r1_tarski @ X0 @ X1)
% 0.57/0.81          | ~ (r2_hidden @ X3 @ X2)
% 0.57/0.81          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 0.57/0.81             (k2_zfmisc_1 @ X2 @ X0)))),
% 0.57/0.81      inference('sup-', [status(thm)], ['1', '2'])).
% 0.57/0.81  thf('4', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.81         (((X0) = (k1_xboole_0))
% 0.57/0.81          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ (sk_C @ X2 @ X1)) @ 
% 0.57/0.81             (k2_zfmisc_1 @ X0 @ X1))
% 0.57/0.81          | (r1_tarski @ X1 @ X2))),
% 0.57/0.81      inference('sup-', [status(thm)], ['0', '3'])).
% 0.57/0.81  thf(t138_zfmisc_1, conjecture,
% 0.57/0.81    (![A:$i,B:$i,C:$i,D:$i]:
% 0.57/0.81     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.57/0.81       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.57/0.81         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 0.57/0.81  thf(zf_stmt_0, negated_conjecture,
% 0.57/0.81    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.57/0.81        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.57/0.81          ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.57/0.81            ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ) )),
% 0.57/0.81    inference('cnf.neg', [status(esa)], [t138_zfmisc_1])).
% 0.57/0.81  thf('5', plain,
% 0.57/0.81      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.57/0.81        (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))),
% 0.57/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.81  thf('6', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.81         (~ (r2_hidden @ X0 @ X1)
% 0.57/0.81          | (r2_hidden @ X0 @ X2)
% 0.57/0.81          | ~ (r1_tarski @ X1 @ X2))),
% 0.57/0.81      inference('cnf', [status(esa)], [d3_tarski])).
% 0.57/0.81  thf('7', plain,
% 0.57/0.81      (![X0 : $i]:
% 0.57/0.81         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))
% 0.57/0.81          | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.57/0.81      inference('sup-', [status(thm)], ['5', '6'])).
% 0.57/0.81  thf('8', plain,
% 0.57/0.81      (![X0 : $i]:
% 0.57/0.81         ((r1_tarski @ sk_B_1 @ X0)
% 0.57/0.81          | ((sk_A) = (k1_xboole_0))
% 0.57/0.81          | (r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ (sk_C @ X0 @ sk_B_1)) @ 
% 0.57/0.81             (k2_zfmisc_1 @ sk_C_2 @ sk_D_1)))),
% 0.57/0.81      inference('sup-', [status(thm)], ['4', '7'])).
% 0.57/0.81  thf('9', plain,
% 0.57/0.81      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.57/0.81         ((r2_hidden @ X34 @ X35)
% 0.57/0.81          | ~ (r2_hidden @ (k4_tarski @ X32 @ X34) @ (k2_zfmisc_1 @ X33 @ X35)))),
% 0.57/0.81      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.57/0.81  thf('10', plain,
% 0.57/0.81      (![X0 : $i]:
% 0.57/0.81         (((sk_A) = (k1_xboole_0))
% 0.57/0.81          | (r1_tarski @ sk_B_1 @ X0)
% 0.57/0.81          | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_D_1))),
% 0.57/0.81      inference('sup-', [status(thm)], ['8', '9'])).
% 0.57/0.81  thf('11', plain,
% 0.57/0.81      (![X1 : $i, X3 : $i]:
% 0.57/0.81         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.57/0.81      inference('cnf', [status(esa)], [d3_tarski])).
% 0.57/0.81  thf('12', plain,
% 0.57/0.81      (((r1_tarski @ sk_B_1 @ sk_D_1)
% 0.57/0.81        | ((sk_A) = (k1_xboole_0))
% 0.57/0.81        | (r1_tarski @ sk_B_1 @ sk_D_1))),
% 0.57/0.81      inference('sup-', [status(thm)], ['10', '11'])).
% 0.57/0.81  thf('13', plain,
% 0.57/0.81      ((((sk_A) = (k1_xboole_0)) | (r1_tarski @ sk_B_1 @ sk_D_1))),
% 0.57/0.81      inference('simplify', [status(thm)], ['12'])).
% 0.57/0.81  thf('14', plain,
% 0.57/0.81      ((~ (r1_tarski @ sk_A @ sk_C_2) | ~ (r1_tarski @ sk_B_1 @ sk_D_1))),
% 0.57/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.81  thf('15', plain,
% 0.57/0.81      ((~ (r1_tarski @ sk_B_1 @ sk_D_1)) <= (~ ((r1_tarski @ sk_B_1 @ sk_D_1)))),
% 0.57/0.81      inference('split', [status(esa)], ['14'])).
% 0.57/0.81  thf('16', plain,
% 0.57/0.81      ((((sk_A) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_B_1 @ sk_D_1)))),
% 0.57/0.81      inference('sup-', [status(thm)], ['13', '15'])).
% 0.57/0.81  thf('17', plain,
% 0.57/0.81      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.57/0.81      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.57/0.81  thf('18', plain,
% 0.57/0.81      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.57/0.81      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.57/0.81  thf('19', plain,
% 0.57/0.81      (![X0 : $i]:
% 0.57/0.81         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))
% 0.57/0.81          | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.57/0.81      inference('sup-', [status(thm)], ['5', '6'])).
% 0.57/0.81  thf('20', plain,
% 0.57/0.81      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.57/0.81        | (r2_hidden @ (sk_B @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) @ 
% 0.57/0.81           (k2_zfmisc_1 @ sk_C_2 @ sk_D_1)))),
% 0.57/0.81      inference('sup-', [status(thm)], ['18', '19'])).
% 0.57/0.81  thf('21', plain, (((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0))),
% 0.57/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.81  thf('22', plain,
% 0.57/0.81      ((r2_hidden @ (sk_B @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) @ 
% 0.57/0.81        (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))),
% 0.57/0.81      inference('simplify_reflect-', [status(thm)], ['20', '21'])).
% 0.57/0.81  thf(t3_xboole_0, axiom,
% 0.57/0.81    (![A:$i,B:$i]:
% 0.57/0.81     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.57/0.81            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.57/0.81       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.57/0.81            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.57/0.81  thf('23', plain,
% 0.57/0.81      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.57/0.81         (~ (r2_hidden @ X6 @ X4)
% 0.57/0.81          | ~ (r2_hidden @ X6 @ X7)
% 0.57/0.81          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.57/0.81      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.57/0.81  thf('24', plain,
% 0.57/0.81      (![X0 : $i]:
% 0.57/0.81         (~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1) @ X0)
% 0.57/0.81          | ~ (r2_hidden @ (sk_B @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) @ X0))),
% 0.57/0.81      inference('sup-', [status(thm)], ['22', '23'])).
% 0.57/0.81  thf('25', plain,
% 0.57/0.81      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.57/0.81        | ~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1) @ 
% 0.57/0.81             (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.57/0.81      inference('sup-', [status(thm)], ['17', '24'])).
% 0.57/0.81  thf('26', plain, (((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0))),
% 0.57/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.81  thf('27', plain,
% 0.57/0.81      (~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1) @ 
% 0.57/0.81          (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.57/0.81      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 0.57/0.81  thf('28', plain,
% 0.57/0.81      ((~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1) @ 
% 0.57/0.81           (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1)))
% 0.57/0.81         <= (~ ((r1_tarski @ sk_B_1 @ sk_D_1)))),
% 0.57/0.81      inference('sup-', [status(thm)], ['16', '27'])).
% 0.57/0.81  thf(t3_boole, axiom,
% 0.57/0.81    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.57/0.81  thf('29', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.57/0.81      inference('cnf', [status(esa)], [t3_boole])).
% 0.57/0.81  thf(t83_xboole_1, axiom,
% 0.57/0.81    (![A:$i,B:$i]:
% 0.57/0.81     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.57/0.81  thf('30', plain,
% 0.57/0.81      (![X13 : $i, X15 : $i]:
% 0.57/0.81         ((r1_xboole_0 @ X13 @ X15) | ((k4_xboole_0 @ X13 @ X15) != (X13)))),
% 0.57/0.81      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.57/0.81  thf('31', plain,
% 0.57/0.81      (![X0 : $i]: (((X0) != (X0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.57/0.81      inference('sup-', [status(thm)], ['29', '30'])).
% 0.57/0.81  thf('32', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.57/0.81      inference('simplify', [status(thm)], ['31'])).
% 0.57/0.81  thf('33', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.57/0.81      inference('simplify', [status(thm)], ['31'])).
% 0.57/0.81  thf(d2_zfmisc_1, axiom,
% 0.57/0.81    (![A:$i,B:$i,C:$i]:
% 0.57/0.81     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.57/0.81       ( ![D:$i]:
% 0.57/0.81         ( ( r2_hidden @ D @ C ) <=>
% 0.57/0.81           ( ?[E:$i,F:$i]:
% 0.57/0.81             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.57/0.81               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.57/0.81  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.57/0.81  thf(zf_stmt_2, axiom,
% 0.57/0.81    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.57/0.81     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.57/0.81       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.57/0.81         ( r2_hidden @ E @ A ) ) ))).
% 0.57/0.81  thf(zf_stmt_3, axiom,
% 0.57/0.81    (![A:$i,B:$i,C:$i]:
% 0.57/0.81     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.57/0.81       ( ![D:$i]:
% 0.57/0.81         ( ( r2_hidden @ D @ C ) <=>
% 0.57/0.81           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.57/0.81  thf('34', plain,
% 0.57/0.81      (![X25 : $i, X26 : $i, X29 : $i]:
% 0.57/0.81         (((X29) = (k2_zfmisc_1 @ X26 @ X25))
% 0.57/0.81          | (zip_tseitin_0 @ (sk_F @ X29 @ X25 @ X26) @ 
% 0.57/0.81             (sk_E @ X29 @ X25 @ X26) @ (sk_D @ X29 @ X25 @ X26) @ X25 @ X26)
% 0.57/0.81          | (r2_hidden @ (sk_D @ X29 @ X25 @ X26) @ X29))),
% 0.57/0.81      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.57/0.81  thf('35', plain,
% 0.57/0.81      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.57/0.81         ((r2_hidden @ X17 @ X19)
% 0.57/0.81          | ~ (zip_tseitin_0 @ X17 @ X16 @ X18 @ X19 @ X20))),
% 0.57/0.81      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.57/0.81  thf('36', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.81         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.57/0.81          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.57/0.81          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.57/0.81      inference('sup-', [status(thm)], ['34', '35'])).
% 0.57/0.81  thf('37', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.81         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.57/0.81          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.57/0.81          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.57/0.81      inference('sup-', [status(thm)], ['34', '35'])).
% 0.57/0.81  thf('38', plain,
% 0.57/0.81      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.57/0.81         (~ (r2_hidden @ X6 @ X4)
% 0.57/0.81          | ~ (r2_hidden @ X6 @ X7)
% 0.57/0.81          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.57/0.81      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.57/0.81  thf('39', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.57/0.81         ((r2_hidden @ (sk_F @ X0 @ X2 @ X1) @ X2)
% 0.57/0.81          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.57/0.81          | ~ (r1_xboole_0 @ X0 @ X3)
% 0.57/0.81          | ~ (r2_hidden @ (sk_D @ X0 @ X2 @ X1) @ X3))),
% 0.57/0.81      inference('sup-', [status(thm)], ['37', '38'])).
% 0.57/0.81  thf('40', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.81         ((r2_hidden @ (sk_F @ X0 @ X2 @ X1) @ X2)
% 0.57/0.81          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.57/0.81          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.57/0.81          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.57/0.81          | (r2_hidden @ (sk_F @ X0 @ X2 @ X1) @ X2))),
% 0.57/0.81      inference('sup-', [status(thm)], ['36', '39'])).
% 0.57/0.81  thf('41', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.81         (~ (r1_xboole_0 @ X0 @ X0)
% 0.57/0.81          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.57/0.81          | (r2_hidden @ (sk_F @ X0 @ X2 @ X1) @ X2))),
% 0.57/0.81      inference('simplify', [status(thm)], ['40'])).
% 0.57/0.81  thf('42', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i]:
% 0.57/0.81         ((r2_hidden @ (sk_F @ k1_xboole_0 @ X0 @ X1) @ X0)
% 0.57/0.81          | ((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0)))),
% 0.57/0.81      inference('sup-', [status(thm)], ['33', '41'])).
% 0.57/0.81  thf('43', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i]:
% 0.57/0.81         ((r2_hidden @ (sk_F @ k1_xboole_0 @ X0 @ X1) @ X0)
% 0.57/0.81          | ((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0)))),
% 0.57/0.81      inference('sup-', [status(thm)], ['33', '41'])).
% 0.57/0.81  thf('44', plain,
% 0.57/0.81      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.57/0.81         (~ (r2_hidden @ X6 @ X4)
% 0.57/0.81          | ~ (r2_hidden @ X6 @ X7)
% 0.57/0.81          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.57/0.81      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.57/0.81  thf('45', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.81         (((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0))
% 0.57/0.81          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.57/0.81          | ~ (r2_hidden @ (sk_F @ k1_xboole_0 @ X0 @ X1) @ X2))),
% 0.57/0.81      inference('sup-', [status(thm)], ['43', '44'])).
% 0.57/0.81  thf('46', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i]:
% 0.57/0.81         (((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0))
% 0.57/0.81          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.57/0.81          | ((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0)))),
% 0.57/0.81      inference('sup-', [status(thm)], ['42', '45'])).
% 0.57/0.81  thf('47', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i]:
% 0.57/0.81         (~ (r1_xboole_0 @ X0 @ X0) | ((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0)))),
% 0.57/0.81      inference('simplify', [status(thm)], ['46'])).
% 0.57/0.81  thf('48', plain,
% 0.57/0.81      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ k1_xboole_0))),
% 0.57/0.81      inference('sup-', [status(thm)], ['32', '47'])).
% 0.57/0.81  thf('49', plain,
% 0.57/0.81      (![X1 : $i, X3 : $i]:
% 0.57/0.81         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.57/0.81      inference('cnf', [status(esa)], [d3_tarski])).
% 0.57/0.81  thf('50', plain,
% 0.57/0.81      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.57/0.81      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.57/0.81  thf('51', plain,
% 0.57/0.81      (![X32 : $i, X33 : $i, X34 : $i, X36 : $i]:
% 0.57/0.81         ((r2_hidden @ (k4_tarski @ X32 @ X34) @ (k2_zfmisc_1 @ X33 @ X36))
% 0.57/0.81          | ~ (r2_hidden @ X34 @ X36)
% 0.57/0.81          | ~ (r2_hidden @ X32 @ X33))),
% 0.57/0.81      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.57/0.81  thf('52', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.81         (((X0) = (k1_xboole_0))
% 0.57/0.81          | ~ (r2_hidden @ X2 @ X1)
% 0.57/0.81          | (r2_hidden @ (k4_tarski @ X2 @ (sk_B @ X0)) @ 
% 0.57/0.81             (k2_zfmisc_1 @ X1 @ X0)))),
% 0.57/0.81      inference('sup-', [status(thm)], ['50', '51'])).
% 0.57/0.81  thf('53', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.81         ((r1_tarski @ X0 @ X1)
% 0.57/0.81          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_B @ X2)) @ 
% 0.57/0.81             (k2_zfmisc_1 @ X0 @ X2))
% 0.57/0.81          | ((X2) = (k1_xboole_0)))),
% 0.57/0.81      inference('sup-', [status(thm)], ['49', '52'])).
% 0.57/0.81  thf('54', plain,
% 0.57/0.81      (![X0 : $i]:
% 0.57/0.81         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))
% 0.57/0.81          | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.57/0.81      inference('sup-', [status(thm)], ['5', '6'])).
% 0.57/0.81  thf('55', plain,
% 0.57/0.81      (![X0 : $i]:
% 0.57/0.81         (((sk_B_1) = (k1_xboole_0))
% 0.57/0.81          | (r1_tarski @ sk_A @ X0)
% 0.57/0.81          | (r2_hidden @ (k4_tarski @ (sk_C @ X0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.57/0.81             (k2_zfmisc_1 @ sk_C_2 @ sk_D_1)))),
% 0.57/0.81      inference('sup-', [status(thm)], ['53', '54'])).
% 0.57/0.81  thf('56', plain,
% 0.57/0.81      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.57/0.81         ((r2_hidden @ X32 @ X33)
% 0.57/0.81          | ~ (r2_hidden @ (k4_tarski @ X32 @ X34) @ (k2_zfmisc_1 @ X33 @ X35)))),
% 0.57/0.81      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.57/0.81  thf('57', plain,
% 0.57/0.81      (![X0 : $i]:
% 0.57/0.81         ((r1_tarski @ sk_A @ X0)
% 0.57/0.81          | ((sk_B_1) = (k1_xboole_0))
% 0.57/0.81          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_C_2))),
% 0.57/0.81      inference('sup-', [status(thm)], ['55', '56'])).
% 0.57/0.81  thf('58', plain,
% 0.57/0.81      (![X1 : $i, X3 : $i]:
% 0.57/0.81         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.57/0.81      inference('cnf', [status(esa)], [d3_tarski])).
% 0.57/0.81  thf('59', plain,
% 0.57/0.81      ((((sk_B_1) = (k1_xboole_0))
% 0.57/0.81        | (r1_tarski @ sk_A @ sk_C_2)
% 0.57/0.81        | (r1_tarski @ sk_A @ sk_C_2))),
% 0.57/0.81      inference('sup-', [status(thm)], ['57', '58'])).
% 0.57/0.81  thf('60', plain,
% 0.57/0.81      (((r1_tarski @ sk_A @ sk_C_2) | ((sk_B_1) = (k1_xboole_0)))),
% 0.57/0.81      inference('simplify', [status(thm)], ['59'])).
% 0.57/0.81  thf('61', plain,
% 0.57/0.81      ((~ (r1_tarski @ sk_A @ sk_C_2)) <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 0.57/0.81      inference('split', [status(esa)], ['14'])).
% 0.57/0.81  thf('62', plain,
% 0.57/0.81      ((((sk_B_1) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 0.57/0.81      inference('sup-', [status(thm)], ['60', '61'])).
% 0.57/0.81  thf('63', plain, (((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0))),
% 0.57/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.81  thf('64', plain,
% 0.57/0.81      ((((k2_zfmisc_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.57/0.81         <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 0.57/0.81      inference('sup-', [status(thm)], ['62', '63'])).
% 0.57/0.81  thf('65', plain,
% 0.57/0.81      ((((k1_xboole_0) != (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 0.57/0.81      inference('sup-', [status(thm)], ['48', '64'])).
% 0.57/0.81  thf('66', plain, (((r1_tarski @ sk_A @ sk_C_2))),
% 0.57/0.81      inference('simplify', [status(thm)], ['65'])).
% 0.57/0.81  thf('67', plain,
% 0.57/0.81      (~ ((r1_tarski @ sk_B_1 @ sk_D_1)) | ~ ((r1_tarski @ sk_A @ sk_C_2))),
% 0.57/0.81      inference('split', [status(esa)], ['14'])).
% 0.57/0.81  thf('68', plain, (~ ((r1_tarski @ sk_B_1 @ sk_D_1))),
% 0.57/0.81      inference('sat_resolution*', [status(thm)], ['66', '67'])).
% 0.57/0.81  thf('69', plain,
% 0.57/0.81      (~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1) @ 
% 0.57/0.81          (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))),
% 0.57/0.81      inference('simpl_trail', [status(thm)], ['28', '68'])).
% 0.57/0.81  thf('70', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.57/0.81      inference('simplify', [status(thm)], ['31'])).
% 0.57/0.81  thf('71', plain,
% 0.57/0.81      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.57/0.81      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.57/0.81  thf('72', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.57/0.81      inference('simplify', [status(thm)], ['31'])).
% 0.57/0.81  thf('73', plain,
% 0.57/0.81      (![X1 : $i, X3 : $i]:
% 0.57/0.81         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.57/0.81      inference('cnf', [status(esa)], [d3_tarski])).
% 0.57/0.81  thf('74', plain,
% 0.57/0.81      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.57/0.81         (~ (r2_hidden @ X28 @ X27)
% 0.57/0.81          | (zip_tseitin_0 @ (sk_F_1 @ X28 @ X25 @ X26) @ 
% 0.57/0.81             (sk_E_1 @ X28 @ X25 @ X26) @ X28 @ X25 @ X26)
% 0.57/0.81          | ((X27) != (k2_zfmisc_1 @ X26 @ X25)))),
% 0.57/0.81      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.57/0.81  thf('75', plain,
% 0.57/0.81      (![X25 : $i, X26 : $i, X28 : $i]:
% 0.57/0.81         ((zip_tseitin_0 @ (sk_F_1 @ X28 @ X25 @ X26) @ 
% 0.57/0.81           (sk_E_1 @ X28 @ X25 @ X26) @ X28 @ X25 @ X26)
% 0.57/0.81          | ~ (r2_hidden @ X28 @ (k2_zfmisc_1 @ X26 @ X25)))),
% 0.57/0.81      inference('simplify', [status(thm)], ['74'])).
% 0.57/0.81  thf('76', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.81         ((r1_tarski @ (k2_zfmisc_1 @ X1 @ X0) @ X2)
% 0.57/0.81          | (zip_tseitin_0 @ 
% 0.57/0.81             (sk_F_1 @ (sk_C @ X2 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.57/0.81             (sk_E_1 @ (sk_C @ X2 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.57/0.81             (sk_C @ X2 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1))),
% 0.57/0.81      inference('sup-', [status(thm)], ['73', '75'])).
% 0.57/0.81  thf('77', plain,
% 0.57/0.81      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.57/0.81         ((r2_hidden @ X16 @ X20)
% 0.57/0.81          | ~ (zip_tseitin_0 @ X17 @ X16 @ X18 @ X19 @ X20))),
% 0.57/0.81      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.57/0.81  thf('78', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.81         ((r1_tarski @ (k2_zfmisc_1 @ X0 @ X1) @ X2)
% 0.57/0.81          | (r2_hidden @ 
% 0.57/0.81             (sk_E_1 @ (sk_C @ X2 @ (k2_zfmisc_1 @ X0 @ X1)) @ X1 @ X0) @ X0))),
% 0.57/0.81      inference('sup-', [status(thm)], ['76', '77'])).
% 0.57/0.81  thf('79', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.81         ((r1_tarski @ (k2_zfmisc_1 @ X0 @ X1) @ X2)
% 0.57/0.81          | (r2_hidden @ 
% 0.57/0.81             (sk_E_1 @ (sk_C @ X2 @ (k2_zfmisc_1 @ X0 @ X1)) @ X1 @ X0) @ X0))),
% 0.57/0.81      inference('sup-', [status(thm)], ['76', '77'])).
% 0.57/0.81  thf('80', plain,
% 0.57/0.81      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.57/0.81         (~ (r2_hidden @ X6 @ X4)
% 0.57/0.81          | ~ (r2_hidden @ X6 @ X7)
% 0.57/0.81          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.57/0.81      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.57/0.81  thf('81', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.57/0.81         ((r1_tarski @ (k2_zfmisc_1 @ X0 @ X1) @ X2)
% 0.57/0.81          | ~ (r1_xboole_0 @ X0 @ X3)
% 0.57/0.81          | ~ (r2_hidden @ 
% 0.57/0.81               (sk_E_1 @ (sk_C @ X2 @ (k2_zfmisc_1 @ X0 @ X1)) @ X1 @ X0) @ X3))),
% 0.57/0.81      inference('sup-', [status(thm)], ['79', '80'])).
% 0.57/0.81  thf('82', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.81         ((r1_tarski @ (k2_zfmisc_1 @ X0 @ X1) @ X2)
% 0.57/0.81          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.57/0.81          | (r1_tarski @ (k2_zfmisc_1 @ X0 @ X1) @ X2))),
% 0.57/0.81      inference('sup-', [status(thm)], ['78', '81'])).
% 0.57/0.81  thf('83', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.81         (~ (r1_xboole_0 @ X0 @ X0)
% 0.57/0.81          | (r1_tarski @ (k2_zfmisc_1 @ X0 @ X1) @ X2))),
% 0.57/0.81      inference('simplify', [status(thm)], ['82'])).
% 0.57/0.81  thf('84', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i]: (r1_tarski @ (k2_zfmisc_1 @ k1_xboole_0 @ X1) @ X0)),
% 0.57/0.81      inference('sup-', [status(thm)], ['72', '83'])).
% 0.57/0.81  thf('85', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.81         (~ (r2_hidden @ X0 @ X1)
% 0.57/0.81          | (r2_hidden @ X0 @ X2)
% 0.57/0.81          | ~ (r1_tarski @ X1 @ X2))),
% 0.57/0.81      inference('cnf', [status(esa)], [d3_tarski])).
% 0.57/0.81  thf('86', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.81         ((r2_hidden @ X2 @ X0)
% 0.57/0.81          | ~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ k1_xboole_0 @ X1)))),
% 0.57/0.81      inference('sup-', [status(thm)], ['84', '85'])).
% 0.57/0.81  thf('87', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i]:
% 0.57/0.81         (((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.57/0.81          | (r2_hidden @ (sk_B @ (k2_zfmisc_1 @ k1_xboole_0 @ X0)) @ X1))),
% 0.57/0.81      inference('sup-', [status(thm)], ['71', '86'])).
% 0.57/0.81  thf('88', plain,
% 0.57/0.81      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.57/0.81      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.57/0.81  thf('89', plain,
% 0.57/0.81      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.57/0.81         (~ (r2_hidden @ X6 @ X4)
% 0.57/0.81          | ~ (r2_hidden @ X6 @ X7)
% 0.57/0.81          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.57/0.81      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.57/0.81  thf('90', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i]:
% 0.57/0.81         (((X0) = (k1_xboole_0))
% 0.57/0.81          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.57/0.81          | ~ (r2_hidden @ (sk_B @ X0) @ X1))),
% 0.57/0.81      inference('sup-', [status(thm)], ['88', '89'])).
% 0.57/0.81  thf('91', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i]:
% 0.57/0.81         (((k2_zfmisc_1 @ k1_xboole_0 @ X1) = (k1_xboole_0))
% 0.57/0.81          | ~ (r1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ X1) @ X0)
% 0.57/0.81          | ((k2_zfmisc_1 @ k1_xboole_0 @ X1) = (k1_xboole_0)))),
% 0.57/0.81      inference('sup-', [status(thm)], ['87', '90'])).
% 0.57/0.81  thf('92', plain,
% 0.57/0.81      (![X0 : $i, X1 : $i]:
% 0.57/0.81         (~ (r1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ X1) @ X0)
% 0.57/0.81          | ((k2_zfmisc_1 @ k1_xboole_0 @ X1) = (k1_xboole_0)))),
% 0.57/0.81      inference('simplify', [status(thm)], ['91'])).
% 0.57/0.81  thf('93', plain,
% 0.57/0.81      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.57/0.81      inference('sup-', [status(thm)], ['70', '92'])).
% 0.57/0.81  thf('94', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.57/0.81      inference('simplify', [status(thm)], ['31'])).
% 0.57/0.81  thf('95', plain, ($false),
% 0.57/0.81      inference('demod', [status(thm)], ['69', '93', '94'])).
% 0.57/0.81  
% 0.57/0.81  % SZS output end Refutation
% 0.57/0.81  
% 0.57/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
