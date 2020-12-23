%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IGhXSpHxSv

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:37 EST 2020

% Result     : Theorem 24.15s
% Output     : Refutation 24.15s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 467 expanded)
%              Number of leaves         :   30 ( 155 expanded)
%              Depth                    :   23
%              Number of atoms          : 1347 (4872 expanded)
%              Number of equality atoms :   88 ( 483 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t134_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = ( k2_zfmisc_1 @ C @ D ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( ( A = C )
          & ( B = D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( k2_zfmisc_1 @ A @ B )
          = ( k2_zfmisc_1 @ C @ D ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( ( A = C )
            & ( B = D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t134_zfmisc_1])).

thf('0',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('1',plain,(
    ! [X22: $i,X23: $i,X26: $i] :
      ( ( X26
        = ( k2_zfmisc_1 @ X23 @ X22 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X26 @ X22 @ X23 ) @ ( sk_E @ X26 @ X22 @ X23 ) @ ( sk_D @ X26 @ X22 @ X23 ) @ X22 @ X23 )
      | ( r2_hidden @ ( sk_D @ X26 @ X22 @ X23 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X14 @ X16 )
      | ~ ( zip_tseitin_0 @ X14 @ X13 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('7',plain,(
    ! [X12: $i] :
      ( r1_xboole_0 @ X12 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('8',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('10',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k2_zfmisc_1 @ X35 @ X36 )
        = k1_xboole_0 )
      | ( X36 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('11',plain,(
    ! [X35: $i] :
      ( ( k2_zfmisc_1 @ X35 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['9','11'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('14',plain,(
    ! [X29: $i,X30: $i,X31: $i,X33: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X29 @ X31 ) @ ( k2_zfmisc_1 @ X30 @ X33 ) )
      | ~ ( r2_hidden @ X31 @ X33 )
      | ~ ( r2_hidden @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_D @ X0 @ k1_xboole_0 @ X1 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ k1_xboole_0 @ X1 ) @ ( sk_D @ X2 @ k1_xboole_0 @ X3 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_A @ k1_xboole_0 @ X1 ) @ ( sk_D @ sk_B @ k1_xboole_0 @ X0 ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['0','16'])).

thf('18',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_A @ k1_xboole_0 @ X1 ) @ ( sk_D @ sk_B @ k1_xboole_0 @ X0 ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['17','18','19'])).

thf('21',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( r2_hidden @ X31 @ X32 )
      | ~ ( r2_hidden @ ( k4_tarski @ X29 @ X31 ) @ ( k2_zfmisc_1 @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_D @ sk_B @ k1_xboole_0 @ X0 ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('23',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('24',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,(
    ! [X29: $i,X30: $i,X31: $i,X33: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X29 @ X31 ) @ ( k2_zfmisc_1 @ X30 @ X33 ) )
      | ~ ( r2_hidden @ X31 @ X33 )
      | ~ ( r2_hidden @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X3 @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( r1_tarski @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( r2_hidden @ X29 @ X30 )
      | ~ ( r2_hidden @ ( k4_tarski @ X29 @ X31 ) @ ( k2_zfmisc_1 @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) )
      | ( r2_hidden @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_D_1 @ X0 )
      | ( r1_tarski @ sk_C_2 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ sk_C_2 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ sk_A )
      | ( r1_tarski @ sk_D_1 @ X0 )
      | ( r1_tarski @ sk_C_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D_1 @ X0 )
      | ( r1_tarski @ sk_C_2 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_C_2 @ sk_A )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_B @ k1_xboole_0 @ X0 ) @ X1 )
      | ( r1_tarski @ sk_C_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','36'])).

thf('38',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('39',plain,(
    r1_tarski @ sk_C_2 @ sk_A ),
    inference('sup-',[status(thm)],['37','38'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('40',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_2 )
    | ( sk_A = sk_C_2 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_D @ X0 @ k1_xboole_0 @ X1 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_D @ X2 @ k1_xboole_0 @ X3 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ sk_A ) @ ( sk_D @ sk_B @ k1_xboole_0 @ X0 ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) )
      | ( sk_B = k1_xboole_0 )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ sk_A ) @ ( sk_D @ sk_B @ k1_xboole_0 @ X0 ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('50',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['9','11'])).

thf('54',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('55',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X25 @ X24 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X25 @ X22 @ X23 ) @ ( sk_E_1 @ X25 @ X22 @ X23 ) @ X25 @ X22 @ X23 )
      | ( X24
       != ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('57',plain,(
    ! [X22: $i,X23: $i,X25: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X25 @ X22 @ X23 ) @ ( sk_E_1 @ X25 @ X22 @ X23 ) @ X25 @ X22 @ X23 )
      | ~ ( r2_hidden @ X25 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X0 @ sk_B @ sk_A ) @ ( sk_E_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ X0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ) @ sk_B @ sk_A ) @ ( sk_E_1 @ ( sk_C @ X0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ) @ sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ) @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','58'])).

thf('60',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X14 @ X16 )
      | ~ ( zip_tseitin_0 @ X14 @ X13 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) @ X0 )
      | ( r2_hidden @ ( sk_F_1 @ ( sk_C @ X0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ) @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X29: $i,X30: $i,X31: $i,X33: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X29 @ X31 ) @ ( k2_zfmisc_1 @ X30 @ X33 ) )
      | ~ ( r2_hidden @ X31 @ X33 )
      | ~ ( r2_hidden @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) @ X0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_F_1 @ ( sk_C @ X0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ) @ sk_B @ sk_A ) ) @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ k1_xboole_0 @ X1 ) @ ( sk_F_1 @ ( sk_C @ X2 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ) @ sk_B @ sk_A ) ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) )
      | ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['53','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_A @ k1_xboole_0 @ X1 ) @ ( sk_F_1 @ ( sk_C @ X0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ) @ sk_B @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) )
      | ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) @ X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['52','64'])).

thf('66',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_A @ k1_xboole_0 @ X1 ) @ ( sk_F_1 @ ( sk_C @ X0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ) @ sk_B @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) )
      | ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( r2_hidden @ X29 @ X30 )
      | ~ ( r2_hidden @ ( k4_tarski @ X29 @ X31 ) @ ( k2_zfmisc_1 @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ sk_A @ k1_xboole_0 @ X1 ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_A @ k1_xboole_0 @ X1 ) @ sk_C_2 )
      | ~ ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) )
      | ( X0
        = ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) )
      | ( r2_hidden @ ( sk_D @ sk_A @ k1_xboole_0 @ X0 ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['51','71'])).

thf('73',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X34: $i,X35: $i] :
      ( ( X34 = k1_xboole_0 )
      | ( X35 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X35 @ X34 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('75',plain,
    ( ( ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 )
     != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['75','76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_D @ sk_A @ k1_xboole_0 @ X0 ) @ sk_C_2 ) ),
    inference('simplify_reflect-',[status(thm)],['72','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X3 @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( r1_tarski @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('81',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( r2_hidden @ X31 @ X32 )
      | ~ ( r2_hidden @ ( k4_tarski @ X29 @ X31 ) @ ( k2_zfmisc_1 @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_D_1 @ X0 )
      | ( r1_tarski @ sk_C_2 @ X1 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_D_1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r1_tarski @ sk_D_1 @ sk_B )
      | ( r1_tarski @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D_1 @ sk_B )
      | ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_D_1 @ sk_B )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_A @ k1_xboole_0 @ X0 ) @ X1 )
      | ( r1_tarski @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['79','89'])).

thf('91',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('92',plain,(
    r1_tarski @ sk_D_1 @ sk_B ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('94',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D_1 )
    | ( sk_B = sk_D_1 ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['9','11'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ k1_xboole_0 @ X1 ) @ ( sk_C @ X3 @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( r1_tarski @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_A @ k1_xboole_0 @ X1 ) @ ( sk_C @ X0 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['95','98'])).

thf('100',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_A @ k1_xboole_0 @ X1 ) @ ( sk_C @ X0 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( r2_hidden @ X31 @ X32 )
      | ~ ( r2_hidden @ ( k4_tarski @ X29 @ X31 ) @ ( k2_zfmisc_1 @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('105',plain,
    ( ( r1_tarski @ sk_B @ sk_D_1 )
    | ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    r1_tarski @ sk_B @ sk_D_1 ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    sk_B = sk_D_1 ),
    inference(demod,[status(thm)],['94','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ sk_A ) @ ( sk_D @ sk_D_1 @ k1_xboole_0 @ X0 ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference(demod,[status(thm)],['48','107'])).

thf('109',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( r2_hidden @ X29 @ X30 )
      | ~ ( r2_hidden @ ( k4_tarski @ X29 @ X31 ) @ ( k2_zfmisc_1 @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('110',plain,(
    ! [X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ sk_A ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('112',plain,
    ( ( r1_tarski @ sk_A @ sk_C_2 )
    | ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    r1_tarski @ sk_A @ sk_C_2 ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    sk_A = sk_C_2 ),
    inference(demod,[status(thm)],['41','113'])).

thf('115',plain,
    ( ( sk_A != sk_C_2 )
    | ( sk_B != sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( sk_A != sk_C_2 )
   <= ( sk_A != sk_C_2 ) ),
    inference(split,[status(esa)],['115'])).

thf('117',plain,(
    sk_B = sk_D_1 ),
    inference(demod,[status(thm)],['94','106'])).

thf('118',plain,
    ( ( sk_B != sk_D_1 )
   <= ( sk_B != sk_D_1 ) ),
    inference(split,[status(esa)],['115'])).

thf('119',plain,
    ( ( sk_D_1 != sk_D_1 )
   <= ( sk_B != sk_D_1 ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    sk_B = sk_D_1 ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,
    ( ( sk_A != sk_C_2 )
    | ( sk_B != sk_D_1 ) ),
    inference(split,[status(esa)],['115'])).

thf('122',plain,(
    sk_A != sk_C_2 ),
    inference('sat_resolution*',[status(thm)],['120','121'])).

thf('123',plain,(
    sk_A != sk_C_2 ),
    inference(simpl_trail,[status(thm)],['116','122'])).

thf('124',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['114','123'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IGhXSpHxSv
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:09:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 24.15/24.40  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 24.15/24.40  % Solved by: fo/fo7.sh
% 24.15/24.40  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 24.15/24.40  % done 5519 iterations in 23.939s
% 24.15/24.40  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 24.15/24.40  % SZS output start Refutation
% 24.15/24.40  thf(sk_D_1_type, type, sk_D_1: $i).
% 24.15/24.40  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 24.15/24.40  thf(sk_B_type, type, sk_B: $i).
% 24.15/24.40  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 24.15/24.40  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 24.15/24.40  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 24.15/24.40  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 24.15/24.40  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 24.15/24.40  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 24.15/24.40  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 24.15/24.40  thf(sk_A_type, type, sk_A: $i).
% 24.15/24.40  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 24.15/24.40  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i).
% 24.15/24.40  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 24.15/24.40  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 24.15/24.40  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 24.15/24.40  thf(sk_C_2_type, type, sk_C_2: $i).
% 24.15/24.40  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 24.15/24.40  thf(t134_zfmisc_1, conjecture,
% 24.15/24.40    (![A:$i,B:$i,C:$i,D:$i]:
% 24.15/24.40     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 24.15/24.40       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 24.15/24.40         ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ))).
% 24.15/24.40  thf(zf_stmt_0, negated_conjecture,
% 24.15/24.40    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 24.15/24.40        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 24.15/24.40          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 24.15/24.40            ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) )),
% 24.15/24.40    inference('cnf.neg', [status(esa)], [t134_zfmisc_1])).
% 24.15/24.40  thf('0', plain,
% 24.15/24.40      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))),
% 24.15/24.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.15/24.40  thf(d2_zfmisc_1, axiom,
% 24.15/24.40    (![A:$i,B:$i,C:$i]:
% 24.15/24.40     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 24.15/24.40       ( ![D:$i]:
% 24.15/24.40         ( ( r2_hidden @ D @ C ) <=>
% 24.15/24.40           ( ?[E:$i,F:$i]:
% 24.15/24.40             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 24.15/24.40               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 24.15/24.40  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 24.15/24.40  thf(zf_stmt_2, axiom,
% 24.15/24.40    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 24.15/24.40     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 24.15/24.40       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 24.15/24.40         ( r2_hidden @ E @ A ) ) ))).
% 24.15/24.40  thf(zf_stmt_3, axiom,
% 24.15/24.40    (![A:$i,B:$i,C:$i]:
% 24.15/24.40     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 24.15/24.40       ( ![D:$i]:
% 24.15/24.40         ( ( r2_hidden @ D @ C ) <=>
% 24.15/24.40           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 24.15/24.40  thf('1', plain,
% 24.15/24.40      (![X22 : $i, X23 : $i, X26 : $i]:
% 24.15/24.40         (((X26) = (k2_zfmisc_1 @ X23 @ X22))
% 24.15/24.40          | (zip_tseitin_0 @ (sk_F @ X26 @ X22 @ X23) @ 
% 24.15/24.40             (sk_E @ X26 @ X22 @ X23) @ (sk_D @ X26 @ X22 @ X23) @ X22 @ X23)
% 24.15/24.40          | (r2_hidden @ (sk_D @ X26 @ X22 @ X23) @ X26))),
% 24.15/24.40      inference('cnf', [status(esa)], [zf_stmt_3])).
% 24.15/24.40  thf('2', plain,
% 24.15/24.40      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 24.15/24.40         ((r2_hidden @ X14 @ X16)
% 24.15/24.40          | ~ (zip_tseitin_0 @ X14 @ X13 @ X15 @ X16 @ X17))),
% 24.15/24.40      inference('cnf', [status(esa)], [zf_stmt_2])).
% 24.15/24.40  thf('3', plain,
% 24.15/24.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.15/24.40         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 24.15/24.40          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 24.15/24.40          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 24.15/24.40      inference('sup-', [status(thm)], ['1', '2'])).
% 24.15/24.40  thf(t2_boole, axiom,
% 24.15/24.40    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 24.15/24.40  thf('4', plain,
% 24.15/24.40      (![X11 : $i]: ((k3_xboole_0 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 24.15/24.40      inference('cnf', [status(esa)], [t2_boole])).
% 24.15/24.40  thf(t4_xboole_0, axiom,
% 24.15/24.40    (![A:$i,B:$i]:
% 24.15/24.40     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 24.15/24.40            ( r1_xboole_0 @ A @ B ) ) ) & 
% 24.15/24.40       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 24.15/24.40            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 24.15/24.40  thf('5', plain,
% 24.15/24.40      (![X4 : $i, X6 : $i, X7 : $i]:
% 24.15/24.40         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 24.15/24.40          | ~ (r1_xboole_0 @ X4 @ X7))),
% 24.15/24.40      inference('cnf', [status(esa)], [t4_xboole_0])).
% 24.15/24.40  thf('6', plain,
% 24.15/24.40      (![X0 : $i, X1 : $i]:
% 24.15/24.40         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 24.15/24.40      inference('sup-', [status(thm)], ['4', '5'])).
% 24.15/24.40  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 24.15/24.40  thf('7', plain, (![X12 : $i]: (r1_xboole_0 @ X12 @ k1_xboole_0)),
% 24.15/24.40      inference('cnf', [status(esa)], [t65_xboole_1])).
% 24.15/24.40  thf('8', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 24.15/24.40      inference('demod', [status(thm)], ['6', '7'])).
% 24.15/24.40  thf('9', plain,
% 24.15/24.40      (![X0 : $i, X1 : $i]:
% 24.15/24.40         (((X1) = (k2_zfmisc_1 @ X0 @ k1_xboole_0))
% 24.15/24.40          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1))),
% 24.15/24.40      inference('sup-', [status(thm)], ['3', '8'])).
% 24.15/24.40  thf(t113_zfmisc_1, axiom,
% 24.15/24.40    (![A:$i,B:$i]:
% 24.15/24.40     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 24.15/24.40       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 24.15/24.40  thf('10', plain,
% 24.15/24.40      (![X35 : $i, X36 : $i]:
% 24.15/24.40         (((k2_zfmisc_1 @ X35 @ X36) = (k1_xboole_0))
% 24.15/24.40          | ((X36) != (k1_xboole_0)))),
% 24.15/24.40      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 24.15/24.40  thf('11', plain,
% 24.15/24.40      (![X35 : $i]: ((k2_zfmisc_1 @ X35 @ k1_xboole_0) = (k1_xboole_0))),
% 24.15/24.40      inference('simplify', [status(thm)], ['10'])).
% 24.15/24.40  thf('12', plain,
% 24.15/24.40      (![X0 : $i, X1 : $i]:
% 24.15/24.40         (((X1) = (k1_xboole_0))
% 24.15/24.40          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1))),
% 24.15/24.40      inference('demod', [status(thm)], ['9', '11'])).
% 24.15/24.40  thf('13', plain,
% 24.15/24.40      (![X0 : $i, X1 : $i]:
% 24.15/24.40         (((X1) = (k1_xboole_0))
% 24.15/24.40          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1))),
% 24.15/24.40      inference('demod', [status(thm)], ['9', '11'])).
% 24.15/24.40  thf(l54_zfmisc_1, axiom,
% 24.15/24.40    (![A:$i,B:$i,C:$i,D:$i]:
% 24.15/24.40     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 24.15/24.40       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 24.15/24.40  thf('14', plain,
% 24.15/24.40      (![X29 : $i, X30 : $i, X31 : $i, X33 : $i]:
% 24.15/24.40         ((r2_hidden @ (k4_tarski @ X29 @ X31) @ (k2_zfmisc_1 @ X30 @ X33))
% 24.15/24.40          | ~ (r2_hidden @ X31 @ X33)
% 24.15/24.40          | ~ (r2_hidden @ X29 @ X30))),
% 24.15/24.40      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 24.15/24.40  thf('15', plain,
% 24.15/24.40      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 24.15/24.40         (((X0) = (k1_xboole_0))
% 24.15/24.40          | ~ (r2_hidden @ X3 @ X2)
% 24.15/24.40          | (r2_hidden @ (k4_tarski @ X3 @ (sk_D @ X0 @ k1_xboole_0 @ X1)) @ 
% 24.15/24.40             (k2_zfmisc_1 @ X2 @ X0)))),
% 24.15/24.40      inference('sup-', [status(thm)], ['13', '14'])).
% 24.15/24.40  thf('16', plain,
% 24.15/24.40      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 24.15/24.40         (((X0) = (k1_xboole_0))
% 24.15/24.40          | (r2_hidden @ 
% 24.15/24.40             (k4_tarski @ (sk_D @ X0 @ k1_xboole_0 @ X1) @ 
% 24.15/24.40              (sk_D @ X2 @ k1_xboole_0 @ X3)) @ 
% 24.15/24.40             (k2_zfmisc_1 @ X0 @ X2))
% 24.15/24.40          | ((X2) = (k1_xboole_0)))),
% 24.15/24.40      inference('sup-', [status(thm)], ['12', '15'])).
% 24.15/24.40  thf('17', plain,
% 24.15/24.40      (![X0 : $i, X1 : $i]:
% 24.15/24.40         ((r2_hidden @ 
% 24.15/24.40           (k4_tarski @ (sk_D @ sk_A @ k1_xboole_0 @ X1) @ 
% 24.15/24.40            (sk_D @ sk_B @ k1_xboole_0 @ X0)) @ 
% 24.15/24.40           (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))
% 24.15/24.40          | ((sk_B) = (k1_xboole_0))
% 24.15/24.40          | ((sk_A) = (k1_xboole_0)))),
% 24.15/24.40      inference('sup+', [status(thm)], ['0', '16'])).
% 24.15/24.40  thf('18', plain, (((sk_A) != (k1_xboole_0))),
% 24.15/24.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.15/24.40  thf('19', plain, (((sk_B) != (k1_xboole_0))),
% 24.15/24.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.15/24.40  thf('20', plain,
% 24.15/24.40      (![X0 : $i, X1 : $i]:
% 24.15/24.40         (r2_hidden @ 
% 24.15/24.40          (k4_tarski @ (sk_D @ sk_A @ k1_xboole_0 @ X1) @ 
% 24.15/24.40           (sk_D @ sk_B @ k1_xboole_0 @ X0)) @ 
% 24.15/24.40          (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))),
% 24.15/24.40      inference('simplify_reflect-', [status(thm)], ['17', '18', '19'])).
% 24.15/24.40  thf('21', plain,
% 24.15/24.40      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 24.15/24.40         ((r2_hidden @ X31 @ X32)
% 24.15/24.40          | ~ (r2_hidden @ (k4_tarski @ X29 @ X31) @ (k2_zfmisc_1 @ X30 @ X32)))),
% 24.15/24.40      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 24.15/24.40  thf('22', plain,
% 24.15/24.40      (![X0 : $i]: (r2_hidden @ (sk_D @ sk_B @ k1_xboole_0 @ X0) @ sk_D_1)),
% 24.15/24.40      inference('sup-', [status(thm)], ['20', '21'])).
% 24.15/24.40  thf(d3_tarski, axiom,
% 24.15/24.40    (![A:$i,B:$i]:
% 24.15/24.40     ( ( r1_tarski @ A @ B ) <=>
% 24.15/24.40       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 24.15/24.40  thf('23', plain,
% 24.15/24.40      (![X1 : $i, X3 : $i]:
% 24.15/24.40         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 24.15/24.40      inference('cnf', [status(esa)], [d3_tarski])).
% 24.15/24.40  thf('24', plain,
% 24.15/24.40      (![X1 : $i, X3 : $i]:
% 24.15/24.40         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 24.15/24.40      inference('cnf', [status(esa)], [d3_tarski])).
% 24.15/24.40  thf('25', plain,
% 24.15/24.40      (![X29 : $i, X30 : $i, X31 : $i, X33 : $i]:
% 24.15/24.40         ((r2_hidden @ (k4_tarski @ X29 @ X31) @ (k2_zfmisc_1 @ X30 @ X33))
% 24.15/24.40          | ~ (r2_hidden @ X31 @ X33)
% 24.15/24.40          | ~ (r2_hidden @ X29 @ X30))),
% 24.15/24.40      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 24.15/24.40  thf('26', plain,
% 24.15/24.40      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 24.15/24.40         ((r1_tarski @ X0 @ X1)
% 24.15/24.40          | ~ (r2_hidden @ X3 @ X2)
% 24.15/24.40          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 24.15/24.40             (k2_zfmisc_1 @ X2 @ X0)))),
% 24.15/24.40      inference('sup-', [status(thm)], ['24', '25'])).
% 24.15/24.40  thf('27', plain,
% 24.15/24.40      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 24.15/24.40         ((r1_tarski @ X0 @ X1)
% 24.15/24.40          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_C @ X3 @ X2)) @ 
% 24.15/24.40             (k2_zfmisc_1 @ X0 @ X2))
% 24.15/24.40          | (r1_tarski @ X2 @ X3))),
% 24.15/24.40      inference('sup-', [status(thm)], ['23', '26'])).
% 24.15/24.40  thf('28', plain,
% 24.15/24.40      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))),
% 24.15/24.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.15/24.40  thf('29', plain,
% 24.15/24.40      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 24.15/24.40         ((r2_hidden @ X29 @ X30)
% 24.15/24.40          | ~ (r2_hidden @ (k4_tarski @ X29 @ X31) @ (k2_zfmisc_1 @ X30 @ X32)))),
% 24.15/24.40      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 24.15/24.40  thf('30', plain,
% 24.15/24.40      (![X0 : $i, X1 : $i]:
% 24.15/24.40         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ 
% 24.15/24.40             (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))
% 24.15/24.40          | (r2_hidden @ X1 @ sk_A))),
% 24.15/24.40      inference('sup-', [status(thm)], ['28', '29'])).
% 24.15/24.40  thf('31', plain,
% 24.15/24.40      (![X0 : $i, X1 : $i]:
% 24.15/24.40         ((r1_tarski @ sk_D_1 @ X0)
% 24.15/24.40          | (r1_tarski @ sk_C_2 @ X1)
% 24.15/24.40          | (r2_hidden @ (sk_C @ X1 @ sk_C_2) @ sk_A))),
% 24.15/24.40      inference('sup-', [status(thm)], ['27', '30'])).
% 24.15/24.40  thf('32', plain,
% 24.15/24.40      (![X1 : $i, X3 : $i]:
% 24.15/24.40         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 24.15/24.40      inference('cnf', [status(esa)], [d3_tarski])).
% 24.15/24.40  thf('33', plain,
% 24.15/24.40      (![X0 : $i]:
% 24.15/24.40         ((r1_tarski @ sk_C_2 @ sk_A)
% 24.15/24.40          | (r1_tarski @ sk_D_1 @ X0)
% 24.15/24.40          | (r1_tarski @ sk_C_2 @ sk_A))),
% 24.15/24.40      inference('sup-', [status(thm)], ['31', '32'])).
% 24.15/24.40  thf('34', plain,
% 24.15/24.40      (![X0 : $i]: ((r1_tarski @ sk_D_1 @ X0) | (r1_tarski @ sk_C_2 @ sk_A))),
% 24.15/24.40      inference('simplify', [status(thm)], ['33'])).
% 24.15/24.40  thf('35', plain,
% 24.15/24.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.15/24.40         (~ (r2_hidden @ X0 @ X1)
% 24.15/24.40          | (r2_hidden @ X0 @ X2)
% 24.15/24.40          | ~ (r1_tarski @ X1 @ X2))),
% 24.15/24.40      inference('cnf', [status(esa)], [d3_tarski])).
% 24.15/24.40  thf('36', plain,
% 24.15/24.40      (![X0 : $i, X1 : $i]:
% 24.15/24.40         ((r1_tarski @ sk_C_2 @ sk_A)
% 24.15/24.40          | (r2_hidden @ X1 @ X0)
% 24.15/24.40          | ~ (r2_hidden @ X1 @ sk_D_1))),
% 24.15/24.40      inference('sup-', [status(thm)], ['34', '35'])).
% 24.15/24.40  thf('37', plain,
% 24.15/24.40      (![X0 : $i, X1 : $i]:
% 24.15/24.40         ((r2_hidden @ (sk_D @ sk_B @ k1_xboole_0 @ X0) @ X1)
% 24.15/24.40          | (r1_tarski @ sk_C_2 @ sk_A))),
% 24.15/24.40      inference('sup-', [status(thm)], ['22', '36'])).
% 24.15/24.40  thf('38', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 24.15/24.40      inference('demod', [status(thm)], ['6', '7'])).
% 24.15/24.40  thf('39', plain, ((r1_tarski @ sk_C_2 @ sk_A)),
% 24.15/24.40      inference('sup-', [status(thm)], ['37', '38'])).
% 24.15/24.40  thf(d10_xboole_0, axiom,
% 24.15/24.40    (![A:$i,B:$i]:
% 24.15/24.40     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 24.15/24.40  thf('40', plain,
% 24.15/24.40      (![X8 : $i, X10 : $i]:
% 24.15/24.40         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 24.15/24.40      inference('cnf', [status(esa)], [d10_xboole_0])).
% 24.15/24.40  thf('41', plain, ((~ (r1_tarski @ sk_A @ sk_C_2) | ((sk_A) = (sk_C_2)))),
% 24.15/24.40      inference('sup-', [status(thm)], ['39', '40'])).
% 24.15/24.40  thf('42', plain,
% 24.15/24.40      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))),
% 24.15/24.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.15/24.40  thf('43', plain,
% 24.15/24.40      (![X1 : $i, X3 : $i]:
% 24.15/24.40         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 24.15/24.40      inference('cnf', [status(esa)], [d3_tarski])).
% 24.15/24.40  thf('44', plain,
% 24.15/24.40      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 24.15/24.40         (((X0) = (k1_xboole_0))
% 24.15/24.40          | ~ (r2_hidden @ X3 @ X2)
% 24.15/24.40          | (r2_hidden @ (k4_tarski @ X3 @ (sk_D @ X0 @ k1_xboole_0 @ X1)) @ 
% 24.15/24.40             (k2_zfmisc_1 @ X2 @ X0)))),
% 24.15/24.40      inference('sup-', [status(thm)], ['13', '14'])).
% 24.15/24.40  thf('45', plain,
% 24.15/24.40      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 24.15/24.40         ((r1_tarski @ X0 @ X1)
% 24.15/24.40          | (r2_hidden @ 
% 24.15/24.40             (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_D @ X2 @ k1_xboole_0 @ X3)) @ 
% 24.15/24.40             (k2_zfmisc_1 @ X0 @ X2))
% 24.15/24.40          | ((X2) = (k1_xboole_0)))),
% 24.15/24.40      inference('sup-', [status(thm)], ['43', '44'])).
% 24.15/24.40  thf('46', plain,
% 24.15/24.40      (![X0 : $i, X1 : $i]:
% 24.15/24.40         ((r2_hidden @ 
% 24.15/24.40           (k4_tarski @ (sk_C @ X1 @ sk_A) @ (sk_D @ sk_B @ k1_xboole_0 @ X0)) @ 
% 24.15/24.40           (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))
% 24.15/24.40          | ((sk_B) = (k1_xboole_0))
% 24.15/24.40          | (r1_tarski @ sk_A @ X1))),
% 24.15/24.40      inference('sup+', [status(thm)], ['42', '45'])).
% 24.15/24.40  thf('47', plain, (((sk_B) != (k1_xboole_0))),
% 24.15/24.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.15/24.40  thf('48', plain,
% 24.15/24.40      (![X0 : $i, X1 : $i]:
% 24.15/24.40         ((r2_hidden @ 
% 24.15/24.40           (k4_tarski @ (sk_C @ X1 @ sk_A) @ (sk_D @ sk_B @ k1_xboole_0 @ X0)) @ 
% 24.15/24.40           (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))
% 24.15/24.40          | (r1_tarski @ sk_A @ X1))),
% 24.15/24.40      inference('simplify_reflect-', [status(thm)], ['46', '47'])).
% 24.15/24.40  thf('49', plain,
% 24.15/24.40      (![X1 : $i, X3 : $i]:
% 24.15/24.40         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 24.15/24.40      inference('cnf', [status(esa)], [d3_tarski])).
% 24.15/24.40  thf('50', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 24.15/24.40      inference('demod', [status(thm)], ['6', '7'])).
% 24.15/24.40  thf('51', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 24.15/24.40      inference('sup-', [status(thm)], ['49', '50'])).
% 24.15/24.40  thf('52', plain,
% 24.15/24.40      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))),
% 24.15/24.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.15/24.40  thf('53', plain,
% 24.15/24.40      (![X0 : $i, X1 : $i]:
% 24.15/24.40         (((X1) = (k1_xboole_0))
% 24.15/24.40          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1))),
% 24.15/24.40      inference('demod', [status(thm)], ['9', '11'])).
% 24.15/24.40  thf('54', plain,
% 24.15/24.40      (![X1 : $i, X3 : $i]:
% 24.15/24.40         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 24.15/24.40      inference('cnf', [status(esa)], [d3_tarski])).
% 24.15/24.40  thf('55', plain,
% 24.15/24.40      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))),
% 24.15/24.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.15/24.40  thf('56', plain,
% 24.15/24.40      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 24.15/24.40         (~ (r2_hidden @ X25 @ X24)
% 24.15/24.40          | (zip_tseitin_0 @ (sk_F_1 @ X25 @ X22 @ X23) @ 
% 24.15/24.40             (sk_E_1 @ X25 @ X22 @ X23) @ X25 @ X22 @ X23)
% 24.15/24.40          | ((X24) != (k2_zfmisc_1 @ X23 @ X22)))),
% 24.15/24.40      inference('cnf', [status(esa)], [zf_stmt_3])).
% 24.15/24.40  thf('57', plain,
% 24.15/24.40      (![X22 : $i, X23 : $i, X25 : $i]:
% 24.15/24.40         ((zip_tseitin_0 @ (sk_F_1 @ X25 @ X22 @ X23) @ 
% 24.15/24.40           (sk_E_1 @ X25 @ X22 @ X23) @ X25 @ X22 @ X23)
% 24.15/24.40          | ~ (r2_hidden @ X25 @ (k2_zfmisc_1 @ X23 @ X22)))),
% 24.15/24.40      inference('simplify', [status(thm)], ['56'])).
% 24.15/24.40  thf('58', plain,
% 24.15/24.40      (![X0 : $i]:
% 24.15/24.40         (~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))
% 24.15/24.40          | (zip_tseitin_0 @ (sk_F_1 @ X0 @ sk_B @ sk_A) @ 
% 24.15/24.40             (sk_E_1 @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A))),
% 24.15/24.40      inference('sup-', [status(thm)], ['55', '57'])).
% 24.15/24.40  thf('59', plain,
% 24.15/24.40      (![X0 : $i]:
% 24.15/24.40         ((r1_tarski @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1) @ X0)
% 24.15/24.40          | (zip_tseitin_0 @ 
% 24.15/24.40             (sk_F_1 @ (sk_C @ X0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1)) @ sk_B @ 
% 24.15/24.40              sk_A) @ 
% 24.15/24.40             (sk_E_1 @ (sk_C @ X0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1)) @ sk_B @ 
% 24.15/24.40              sk_A) @ 
% 24.15/24.40             (sk_C @ X0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1)) @ sk_B @ sk_A))),
% 24.15/24.40      inference('sup-', [status(thm)], ['54', '58'])).
% 24.15/24.40  thf('60', plain,
% 24.15/24.40      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 24.15/24.40         ((r2_hidden @ X14 @ X16)
% 24.15/24.40          | ~ (zip_tseitin_0 @ X14 @ X13 @ X15 @ X16 @ X17))),
% 24.15/24.40      inference('cnf', [status(esa)], [zf_stmt_2])).
% 24.15/24.40  thf('61', plain,
% 24.15/24.40      (![X0 : $i]:
% 24.15/24.40         ((r1_tarski @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1) @ X0)
% 24.15/24.40          | (r2_hidden @ 
% 24.15/24.40             (sk_F_1 @ (sk_C @ X0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1)) @ sk_B @ 
% 24.15/24.40              sk_A) @ 
% 24.15/24.40             sk_B))),
% 24.15/24.40      inference('sup-', [status(thm)], ['59', '60'])).
% 24.15/24.40  thf('62', plain,
% 24.15/24.40      (![X29 : $i, X30 : $i, X31 : $i, X33 : $i]:
% 24.15/24.40         ((r2_hidden @ (k4_tarski @ X29 @ X31) @ (k2_zfmisc_1 @ X30 @ X33))
% 24.15/24.40          | ~ (r2_hidden @ X31 @ X33)
% 24.15/24.40          | ~ (r2_hidden @ X29 @ X30))),
% 24.15/24.40      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 24.15/24.40  thf('63', plain,
% 24.15/24.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.15/24.40         ((r1_tarski @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1) @ X0)
% 24.15/24.40          | ~ (r2_hidden @ X2 @ X1)
% 24.15/24.40          | (r2_hidden @ 
% 24.15/24.40             (k4_tarski @ X2 @ 
% 24.15/24.40              (sk_F_1 @ (sk_C @ X0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1)) @ sk_B @ 
% 24.15/24.40               sk_A)) @ 
% 24.15/24.40             (k2_zfmisc_1 @ X1 @ sk_B)))),
% 24.15/24.40      inference('sup-', [status(thm)], ['61', '62'])).
% 24.15/24.40  thf('64', plain,
% 24.15/24.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.15/24.40         (((X0) = (k1_xboole_0))
% 24.15/24.40          | (r2_hidden @ 
% 24.15/24.40             (k4_tarski @ (sk_D @ X0 @ k1_xboole_0 @ X1) @ 
% 24.15/24.40              (sk_F_1 @ (sk_C @ X2 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1)) @ sk_B @ 
% 24.15/24.40               sk_A)) @ 
% 24.15/24.40             (k2_zfmisc_1 @ X0 @ sk_B))
% 24.15/24.40          | (r1_tarski @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1) @ X2))),
% 24.15/24.40      inference('sup-', [status(thm)], ['53', '63'])).
% 24.15/24.40  thf('65', plain,
% 24.15/24.40      (![X0 : $i, X1 : $i]:
% 24.15/24.40         ((r2_hidden @ 
% 24.15/24.40           (k4_tarski @ (sk_D @ sk_A @ k1_xboole_0 @ X1) @ 
% 24.15/24.40            (sk_F_1 @ (sk_C @ X0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1)) @ sk_B @ 
% 24.15/24.40             sk_A)) @ 
% 24.15/24.40           (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))
% 24.15/24.40          | (r1_tarski @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1) @ X0)
% 24.15/24.40          | ((sk_A) = (k1_xboole_0)))),
% 24.15/24.40      inference('sup+', [status(thm)], ['52', '64'])).
% 24.15/24.40  thf('66', plain, (((sk_A) != (k1_xboole_0))),
% 24.15/24.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.15/24.40  thf('67', plain,
% 24.15/24.40      (![X0 : $i, X1 : $i]:
% 24.15/24.40         ((r2_hidden @ 
% 24.15/24.40           (k4_tarski @ (sk_D @ sk_A @ k1_xboole_0 @ X1) @ 
% 24.15/24.40            (sk_F_1 @ (sk_C @ X0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1)) @ sk_B @ 
% 24.15/24.40             sk_A)) @ 
% 24.15/24.40           (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))
% 24.15/24.40          | (r1_tarski @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1) @ X0))),
% 24.15/24.40      inference('simplify_reflect-', [status(thm)], ['65', '66'])).
% 24.15/24.40  thf('68', plain,
% 24.15/24.40      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 24.15/24.40         ((r2_hidden @ X29 @ X30)
% 24.15/24.40          | ~ (r2_hidden @ (k4_tarski @ X29 @ X31) @ (k2_zfmisc_1 @ X30 @ X32)))),
% 24.15/24.40      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 24.15/24.40  thf('69', plain,
% 24.15/24.40      (![X0 : $i, X1 : $i]:
% 24.15/24.40         ((r1_tarski @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1) @ X0)
% 24.15/24.40          | (r2_hidden @ (sk_D @ sk_A @ k1_xboole_0 @ X1) @ sk_C_2))),
% 24.15/24.40      inference('sup-', [status(thm)], ['67', '68'])).
% 24.15/24.40  thf('70', plain,
% 24.15/24.40      (![X8 : $i, X10 : $i]:
% 24.15/24.40         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 24.15/24.40      inference('cnf', [status(esa)], [d10_xboole_0])).
% 24.15/24.40  thf('71', plain,
% 24.15/24.40      (![X0 : $i, X1 : $i]:
% 24.15/24.40         ((r2_hidden @ (sk_D @ sk_A @ k1_xboole_0 @ X1) @ sk_C_2)
% 24.15/24.40          | ~ (r1_tarski @ X0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))
% 24.15/24.40          | ((X0) = (k2_zfmisc_1 @ sk_C_2 @ sk_D_1)))),
% 24.15/24.40      inference('sup-', [status(thm)], ['69', '70'])).
% 24.15/24.40  thf('72', plain,
% 24.15/24.40      (![X0 : $i]:
% 24.15/24.40         (((k1_xboole_0) = (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))
% 24.15/24.40          | (r2_hidden @ (sk_D @ sk_A @ k1_xboole_0 @ X0) @ sk_C_2))),
% 24.15/24.40      inference('sup-', [status(thm)], ['51', '71'])).
% 24.15/24.40  thf('73', plain,
% 24.15/24.40      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))),
% 24.15/24.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.15/24.40  thf('74', plain,
% 24.15/24.40      (![X34 : $i, X35 : $i]:
% 24.15/24.40         (((X34) = (k1_xboole_0))
% 24.15/24.40          | ((X35) = (k1_xboole_0))
% 24.15/24.40          | ((k2_zfmisc_1 @ X35 @ X34) != (k1_xboole_0)))),
% 24.15/24.40      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 24.15/24.40  thf('75', plain,
% 24.15/24.40      ((((k2_zfmisc_1 @ sk_C_2 @ sk_D_1) != (k1_xboole_0))
% 24.15/24.40        | ((sk_A) = (k1_xboole_0))
% 24.15/24.40        | ((sk_B) = (k1_xboole_0)))),
% 24.15/24.40      inference('sup-', [status(thm)], ['73', '74'])).
% 24.15/24.40  thf('76', plain, (((sk_B) != (k1_xboole_0))),
% 24.15/24.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.15/24.40  thf('77', plain, (((sk_A) != (k1_xboole_0))),
% 24.15/24.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.15/24.40  thf('78', plain, (((k2_zfmisc_1 @ sk_C_2 @ sk_D_1) != (k1_xboole_0))),
% 24.15/24.40      inference('simplify_reflect-', [status(thm)], ['75', '76', '77'])).
% 24.15/24.40  thf('79', plain,
% 24.15/24.40      (![X0 : $i]: (r2_hidden @ (sk_D @ sk_A @ k1_xboole_0 @ X0) @ sk_C_2)),
% 24.15/24.40      inference('simplify_reflect-', [status(thm)], ['72', '78'])).
% 24.15/24.40  thf('80', plain,
% 24.15/24.40      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 24.15/24.40         ((r1_tarski @ X0 @ X1)
% 24.15/24.40          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_C @ X3 @ X2)) @ 
% 24.15/24.40             (k2_zfmisc_1 @ X0 @ X2))
% 24.15/24.40          | (r1_tarski @ X2 @ X3))),
% 24.15/24.40      inference('sup-', [status(thm)], ['23', '26'])).
% 24.15/24.40  thf('81', plain,
% 24.15/24.40      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))),
% 24.15/24.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.15/24.40  thf('82', plain,
% 24.15/24.40      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 24.15/24.40         ((r2_hidden @ X31 @ X32)
% 24.15/24.40          | ~ (r2_hidden @ (k4_tarski @ X29 @ X31) @ (k2_zfmisc_1 @ X30 @ X32)))),
% 24.15/24.40      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 24.15/24.40  thf('83', plain,
% 24.15/24.40      (![X0 : $i, X1 : $i]:
% 24.15/24.40         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ 
% 24.15/24.40             (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))
% 24.15/24.40          | (r2_hidden @ X0 @ sk_B))),
% 24.15/24.40      inference('sup-', [status(thm)], ['81', '82'])).
% 24.15/24.40  thf('84', plain,
% 24.15/24.40      (![X0 : $i, X1 : $i]:
% 24.15/24.40         ((r1_tarski @ sk_D_1 @ X0)
% 24.15/24.40          | (r1_tarski @ sk_C_2 @ X1)
% 24.15/24.40          | (r2_hidden @ (sk_C @ X0 @ sk_D_1) @ sk_B))),
% 24.15/24.40      inference('sup-', [status(thm)], ['80', '83'])).
% 24.15/24.40  thf('85', plain,
% 24.15/24.40      (![X1 : $i, X3 : $i]:
% 24.15/24.40         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 24.15/24.40      inference('cnf', [status(esa)], [d3_tarski])).
% 24.15/24.40  thf('86', plain,
% 24.15/24.40      (![X0 : $i]:
% 24.15/24.40         ((r1_tarski @ sk_C_2 @ X0)
% 24.15/24.40          | (r1_tarski @ sk_D_1 @ sk_B)
% 24.15/24.40          | (r1_tarski @ sk_D_1 @ sk_B))),
% 24.15/24.40      inference('sup-', [status(thm)], ['84', '85'])).
% 24.15/24.40  thf('87', plain,
% 24.15/24.40      (![X0 : $i]: ((r1_tarski @ sk_D_1 @ sk_B) | (r1_tarski @ sk_C_2 @ X0))),
% 24.15/24.40      inference('simplify', [status(thm)], ['86'])).
% 24.15/24.40  thf('88', plain,
% 24.15/24.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.15/24.40         (~ (r2_hidden @ X0 @ X1)
% 24.15/24.40          | (r2_hidden @ X0 @ X2)
% 24.15/24.40          | ~ (r1_tarski @ X1 @ X2))),
% 24.15/24.40      inference('cnf', [status(esa)], [d3_tarski])).
% 24.15/24.40  thf('89', plain,
% 24.15/24.40      (![X0 : $i, X1 : $i]:
% 24.15/24.40         ((r1_tarski @ sk_D_1 @ sk_B)
% 24.15/24.40          | (r2_hidden @ X1 @ X0)
% 24.15/24.40          | ~ (r2_hidden @ X1 @ sk_C_2))),
% 24.15/24.40      inference('sup-', [status(thm)], ['87', '88'])).
% 24.15/24.40  thf('90', plain,
% 24.15/24.40      (![X0 : $i, X1 : $i]:
% 24.15/24.40         ((r2_hidden @ (sk_D @ sk_A @ k1_xboole_0 @ X0) @ X1)
% 24.15/24.40          | (r1_tarski @ sk_D_1 @ sk_B))),
% 24.15/24.40      inference('sup-', [status(thm)], ['79', '89'])).
% 24.15/24.40  thf('91', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 24.15/24.40      inference('demod', [status(thm)], ['6', '7'])).
% 24.15/24.40  thf('92', plain, ((r1_tarski @ sk_D_1 @ sk_B)),
% 24.15/24.40      inference('sup-', [status(thm)], ['90', '91'])).
% 24.15/24.40  thf('93', plain,
% 24.15/24.40      (![X8 : $i, X10 : $i]:
% 24.15/24.40         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 24.15/24.40      inference('cnf', [status(esa)], [d10_xboole_0])).
% 24.15/24.40  thf('94', plain, ((~ (r1_tarski @ sk_B @ sk_D_1) | ((sk_B) = (sk_D_1)))),
% 24.15/24.40      inference('sup-', [status(thm)], ['92', '93'])).
% 24.15/24.40  thf('95', plain,
% 24.15/24.40      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))),
% 24.15/24.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.15/24.40  thf('96', plain,
% 24.15/24.40      (![X0 : $i, X1 : $i]:
% 24.15/24.40         (((X1) = (k1_xboole_0))
% 24.15/24.40          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1))),
% 24.15/24.40      inference('demod', [status(thm)], ['9', '11'])).
% 24.15/24.40  thf('97', plain,
% 24.15/24.40      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 24.15/24.40         ((r1_tarski @ X0 @ X1)
% 24.15/24.40          | ~ (r2_hidden @ X3 @ X2)
% 24.15/24.40          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 24.15/24.40             (k2_zfmisc_1 @ X2 @ X0)))),
% 24.15/24.40      inference('sup-', [status(thm)], ['24', '25'])).
% 24.15/24.40  thf('98', plain,
% 24.15/24.40      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 24.15/24.40         (((X0) = (k1_xboole_0))
% 24.15/24.40          | (r2_hidden @ 
% 24.15/24.40             (k4_tarski @ (sk_D @ X0 @ k1_xboole_0 @ X1) @ (sk_C @ X3 @ X2)) @ 
% 24.15/24.40             (k2_zfmisc_1 @ X0 @ X2))
% 24.15/24.40          | (r1_tarski @ X2 @ X3))),
% 24.15/24.40      inference('sup-', [status(thm)], ['96', '97'])).
% 24.15/24.40  thf('99', plain,
% 24.15/24.40      (![X0 : $i, X1 : $i]:
% 24.15/24.40         ((r2_hidden @ 
% 24.15/24.40           (k4_tarski @ (sk_D @ sk_A @ k1_xboole_0 @ X1) @ (sk_C @ X0 @ sk_B)) @ 
% 24.15/24.40           (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))
% 24.15/24.40          | (r1_tarski @ sk_B @ X0)
% 24.15/24.40          | ((sk_A) = (k1_xboole_0)))),
% 24.15/24.40      inference('sup+', [status(thm)], ['95', '98'])).
% 24.15/24.40  thf('100', plain, (((sk_A) != (k1_xboole_0))),
% 24.15/24.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.15/24.40  thf('101', plain,
% 24.15/24.40      (![X0 : $i, X1 : $i]:
% 24.15/24.40         ((r2_hidden @ 
% 24.15/24.40           (k4_tarski @ (sk_D @ sk_A @ k1_xboole_0 @ X1) @ (sk_C @ X0 @ sk_B)) @ 
% 24.15/24.40           (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))
% 24.15/24.40          | (r1_tarski @ sk_B @ X0))),
% 24.15/24.40      inference('simplify_reflect-', [status(thm)], ['99', '100'])).
% 24.15/24.40  thf('102', plain,
% 24.15/24.40      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 24.15/24.40         ((r2_hidden @ X31 @ X32)
% 24.15/24.40          | ~ (r2_hidden @ (k4_tarski @ X29 @ X31) @ (k2_zfmisc_1 @ X30 @ X32)))),
% 24.15/24.40      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 24.15/24.40  thf('103', plain,
% 24.15/24.40      (![X0 : $i]:
% 24.15/24.40         ((r1_tarski @ sk_B @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_D_1))),
% 24.15/24.40      inference('sup-', [status(thm)], ['101', '102'])).
% 24.15/24.40  thf('104', plain,
% 24.15/24.40      (![X1 : $i, X3 : $i]:
% 24.15/24.40         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 24.15/24.40      inference('cnf', [status(esa)], [d3_tarski])).
% 24.15/24.40  thf('105', plain,
% 24.15/24.40      (((r1_tarski @ sk_B @ sk_D_1) | (r1_tarski @ sk_B @ sk_D_1))),
% 24.15/24.40      inference('sup-', [status(thm)], ['103', '104'])).
% 24.15/24.40  thf('106', plain, ((r1_tarski @ sk_B @ sk_D_1)),
% 24.15/24.40      inference('simplify', [status(thm)], ['105'])).
% 24.15/24.40  thf('107', plain, (((sk_B) = (sk_D_1))),
% 24.15/24.40      inference('demod', [status(thm)], ['94', '106'])).
% 24.15/24.40  thf('108', plain,
% 24.15/24.40      (![X0 : $i, X1 : $i]:
% 24.15/24.40         ((r2_hidden @ 
% 24.15/24.40           (k4_tarski @ (sk_C @ X1 @ sk_A) @ (sk_D @ sk_D_1 @ k1_xboole_0 @ X0)) @ 
% 24.15/24.40           (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))
% 24.15/24.40          | (r1_tarski @ sk_A @ X1))),
% 24.15/24.40      inference('demod', [status(thm)], ['48', '107'])).
% 24.15/24.40  thf('109', plain,
% 24.15/24.40      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 24.15/24.40         ((r2_hidden @ X29 @ X30)
% 24.15/24.40          | ~ (r2_hidden @ (k4_tarski @ X29 @ X31) @ (k2_zfmisc_1 @ X30 @ X32)))),
% 24.15/24.40      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 24.15/24.40  thf('110', plain,
% 24.15/24.40      (![X1 : $i]:
% 24.15/24.40         ((r1_tarski @ sk_A @ X1) | (r2_hidden @ (sk_C @ X1 @ sk_A) @ sk_C_2))),
% 24.15/24.40      inference('sup-', [status(thm)], ['108', '109'])).
% 24.15/24.40  thf('111', plain,
% 24.15/24.40      (![X1 : $i, X3 : $i]:
% 24.15/24.40         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 24.15/24.40      inference('cnf', [status(esa)], [d3_tarski])).
% 24.15/24.40  thf('112', plain,
% 24.15/24.40      (((r1_tarski @ sk_A @ sk_C_2) | (r1_tarski @ sk_A @ sk_C_2))),
% 24.15/24.40      inference('sup-', [status(thm)], ['110', '111'])).
% 24.15/24.40  thf('113', plain, ((r1_tarski @ sk_A @ sk_C_2)),
% 24.15/24.40      inference('simplify', [status(thm)], ['112'])).
% 24.15/24.40  thf('114', plain, (((sk_A) = (sk_C_2))),
% 24.15/24.40      inference('demod', [status(thm)], ['41', '113'])).
% 24.15/24.40  thf('115', plain, ((((sk_A) != (sk_C_2)) | ((sk_B) != (sk_D_1)))),
% 24.15/24.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.15/24.40  thf('116', plain, ((((sk_A) != (sk_C_2))) <= (~ (((sk_A) = (sk_C_2))))),
% 24.15/24.40      inference('split', [status(esa)], ['115'])).
% 24.15/24.40  thf('117', plain, (((sk_B) = (sk_D_1))),
% 24.15/24.40      inference('demod', [status(thm)], ['94', '106'])).
% 24.15/24.40  thf('118', plain, ((((sk_B) != (sk_D_1))) <= (~ (((sk_B) = (sk_D_1))))),
% 24.15/24.40      inference('split', [status(esa)], ['115'])).
% 24.15/24.40  thf('119', plain, ((((sk_D_1) != (sk_D_1))) <= (~ (((sk_B) = (sk_D_1))))),
% 24.15/24.40      inference('sup-', [status(thm)], ['117', '118'])).
% 24.15/24.40  thf('120', plain, ((((sk_B) = (sk_D_1)))),
% 24.15/24.40      inference('simplify', [status(thm)], ['119'])).
% 24.15/24.40  thf('121', plain, (~ (((sk_A) = (sk_C_2))) | ~ (((sk_B) = (sk_D_1)))),
% 24.15/24.40      inference('split', [status(esa)], ['115'])).
% 24.15/24.40  thf('122', plain, (~ (((sk_A) = (sk_C_2)))),
% 24.15/24.40      inference('sat_resolution*', [status(thm)], ['120', '121'])).
% 24.15/24.40  thf('123', plain, (((sk_A) != (sk_C_2))),
% 24.15/24.40      inference('simpl_trail', [status(thm)], ['116', '122'])).
% 24.15/24.40  thf('124', plain, ($false),
% 24.15/24.40      inference('simplify_reflect-', [status(thm)], ['114', '123'])).
% 24.15/24.40  
% 24.15/24.40  % SZS output end Refutation
% 24.15/24.40  
% 24.15/24.41  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
