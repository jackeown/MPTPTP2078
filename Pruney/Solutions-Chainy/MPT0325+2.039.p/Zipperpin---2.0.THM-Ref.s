%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TUIqZohDox

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:45 EST 2020

% Result     : Theorem 0.85s
% Output     : Refutation 0.85s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 136 expanded)
%              Number of leaves         :   27 (  54 expanded)
%              Depth                    :   18
%              Number of atoms          :  653 (1147 expanded)
%              Number of equality atoms :   36 (  52 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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

thf('0',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5 = X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('2',plain,(
    ! [X6: $i] :
      ( r1_xboole_0 @ X6 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t55_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        & ( r2_hidden @ A @ C ) ) )).

thf('3',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X28 @ X29 ) @ X30 )
      | ~ ( r2_hidden @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('4',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('7',plain,(
    ! [X23: $i,X24: $i,X25: $i,X27: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X23 @ X25 ) @ ( k2_zfmisc_1 @ X24 @ X27 ) )
      | ~ ( r2_hidden @ X25 @ X27 )
      | ~ ( r2_hidden @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ ( sk_C @ X2 @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r1_tarski @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( k1_xboole_0 = sk_A )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ ( sk_C @ X0 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( r2_hidden @ X25 @ X26 )
      | ~ ( r2_hidden @ ( k4_tarski @ X23 @ X25 ) @ ( k2_zfmisc_1 @ X24 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = sk_A )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,
    ( ( r1_tarski @ sk_B @ sk_D_1 )
    | ( k1_xboole_0 = sk_A )
    | ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k1_xboole_0 = sk_A )
    | ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_2 )
    | ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D_1 )
   <= ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('23',plain,(
    ! [X23: $i,X24: $i,X25: $i,X27: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X23 @ X25 ) @ ( k2_zfmisc_1 @ X24 @ X27 ) )
      | ~ ( r2_hidden @ X25 @ X27 )
      | ~ ( r2_hidden @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_C_1 @ X0 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_C_1 @ X2 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( k1_xboole_0 = X2 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = sk_B )
      | ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_A ) @ ( sk_C_1 @ sk_B @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( r2_hidden @ X23 @ X24 )
      | ~ ( r2_hidden @ ( k4_tarski @ X23 @ X25 ) @ ( k2_zfmisc_1 @ X24 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( k1_xboole_0 = sk_B )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('31',plain,
    ( ( k1_xboole_0 = sk_B )
    | ( r1_tarski @ sk_A @ sk_C_2 )
    | ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r1_tarski @ sk_A @ sk_C_2 )
    | ( k1_xboole_0 = sk_B ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_2 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference(split,[status(esa)],['19'])).

thf('34',plain,
    ( ( k1_xboole_0 = sk_B )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['34','35'])).

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

thf('37',plain,(
    ! [X16: $i,X17: $i,X20: $i] :
      ( ( X20
        = ( k2_zfmisc_1 @ X17 @ X16 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X20 @ X16 @ X17 ) @ ( sk_E @ X20 @ X16 @ X17 ) @ ( sk_D @ X20 @ X16 @ X17 ) @ X16 @ X17 )
      | ( r2_hidden @ ( sk_D @ X20 @ X16 @ X17 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('38',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X8 @ X10 )
      | ~ ( zip_tseitin_0 @ X8 @ X7 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('43',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference(demod,[status(thm)],['36','43'])).

thf('45',plain,(
    r1_tarski @ sk_A @ sk_C_2 ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D_1 )
    | ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference(split,[status(esa)],['19'])).

thf('47',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference('sat_resolution*',[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference(simpl_trail,[status(thm)],['20','47'])).

thf('49',plain,(
    k1_xboole_0 = sk_A ),
    inference(clc,[status(thm)],['18','48'])).

thf('50',plain,(
    ! [X16: $i,X17: $i,X20: $i] :
      ( ( X20
        = ( k2_zfmisc_1 @ X17 @ X16 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X20 @ X16 @ X17 ) @ ( sk_E @ X20 @ X16 @ X17 ) @ ( sk_D @ X20 @ X16 @ X17 ) @ X16 @ X17 )
      | ( r2_hidden @ ( sk_D @ X20 @ X16 @ X17 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('51',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X7 @ X11 )
      | ~ ( zip_tseitin_0 @ X8 @ X7 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('56',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','49','56'])).

thf('58',plain,(
    $false ),
    inference(simplify,[status(thm)],['57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TUIqZohDox
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:21:48 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.85/1.07  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.85/1.07  % Solved by: fo/fo7.sh
% 0.85/1.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.85/1.07  % done 480 iterations in 0.621s
% 0.85/1.07  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.85/1.07  % SZS output start Refutation
% 0.85/1.07  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.85/1.07  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.85/1.07  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.85/1.07  thf(sk_A_type, type, sk_A: $i).
% 0.85/1.07  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.85/1.07  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.85/1.07  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.85/1.07  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.85/1.07  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.85/1.07  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.85/1.07  thf(sk_B_type, type, sk_B: $i).
% 0.85/1.07  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.85/1.07  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.85/1.07  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.85/1.07  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.85/1.07  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.85/1.07  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.85/1.07  thf(t138_zfmisc_1, conjecture,
% 0.85/1.07    (![A:$i,B:$i,C:$i,D:$i]:
% 0.85/1.07     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.85/1.07       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.85/1.07         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 0.85/1.07  thf(zf_stmt_0, negated_conjecture,
% 0.85/1.07    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.85/1.07        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.85/1.07          ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.85/1.07            ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ) )),
% 0.85/1.07    inference('cnf.neg', [status(esa)], [t138_zfmisc_1])).
% 0.85/1.07  thf('0', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.85/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.07  thf(t2_tarski, axiom,
% 0.85/1.07    (![A:$i,B:$i]:
% 0.85/1.07     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.85/1.07       ( ( A ) = ( B ) ) ))).
% 0.85/1.07  thf('1', plain,
% 0.85/1.07      (![X4 : $i, X5 : $i]:
% 0.85/1.07         (((X5) = (X4))
% 0.85/1.07          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X4)
% 0.85/1.07          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X5))),
% 0.85/1.07      inference('cnf', [status(esa)], [t2_tarski])).
% 0.85/1.07  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.85/1.07  thf('2', plain, (![X6 : $i]: (r1_xboole_0 @ X6 @ k1_xboole_0)),
% 0.85/1.07      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.85/1.07  thf(t55_zfmisc_1, axiom,
% 0.85/1.07    (![A:$i,B:$i,C:$i]:
% 0.85/1.07     ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & ( r2_hidden @ A @ C ) ) ))).
% 0.85/1.07  thf('3', plain,
% 0.85/1.07      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.85/1.07         (~ (r1_xboole_0 @ (k2_tarski @ X28 @ X29) @ X30)
% 0.85/1.07          | ~ (r2_hidden @ X28 @ X30))),
% 0.85/1.07      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 0.85/1.07  thf('4', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.85/1.07      inference('sup-', [status(thm)], ['2', '3'])).
% 0.85/1.07  thf('5', plain,
% 0.85/1.07      (![X0 : $i]:
% 0.85/1.07         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.85/1.07          | ((k1_xboole_0) = (X0)))),
% 0.85/1.07      inference('sup-', [status(thm)], ['1', '4'])).
% 0.85/1.07  thf(d3_tarski, axiom,
% 0.85/1.07    (![A:$i,B:$i]:
% 0.85/1.07     ( ( r1_tarski @ A @ B ) <=>
% 0.85/1.07       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.85/1.07  thf('6', plain,
% 0.85/1.07      (![X1 : $i, X3 : $i]:
% 0.85/1.07         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.85/1.07      inference('cnf', [status(esa)], [d3_tarski])).
% 0.85/1.07  thf(l54_zfmisc_1, axiom,
% 0.85/1.07    (![A:$i,B:$i,C:$i,D:$i]:
% 0.85/1.07     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.85/1.07       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.85/1.07  thf('7', plain,
% 0.85/1.07      (![X23 : $i, X24 : $i, X25 : $i, X27 : $i]:
% 0.85/1.07         ((r2_hidden @ (k4_tarski @ X23 @ X25) @ (k2_zfmisc_1 @ X24 @ X27))
% 0.85/1.07          | ~ (r2_hidden @ X25 @ X27)
% 0.85/1.07          | ~ (r2_hidden @ X23 @ X24))),
% 0.85/1.07      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.85/1.07  thf('8', plain,
% 0.85/1.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.85/1.07         ((r1_tarski @ X0 @ X1)
% 0.85/1.07          | ~ (r2_hidden @ X3 @ X2)
% 0.85/1.07          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 0.85/1.07             (k2_zfmisc_1 @ X2 @ X0)))),
% 0.85/1.07      inference('sup-', [status(thm)], ['6', '7'])).
% 0.85/1.07  thf('9', plain,
% 0.85/1.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.07         (((k1_xboole_0) = (X0))
% 0.85/1.07          | (r2_hidden @ 
% 0.85/1.07             (k4_tarski @ (sk_C_1 @ X0 @ k1_xboole_0) @ (sk_C @ X2 @ X1)) @ 
% 0.85/1.07             (k2_zfmisc_1 @ X0 @ X1))
% 0.85/1.07          | (r1_tarski @ X1 @ X2))),
% 0.85/1.07      inference('sup-', [status(thm)], ['5', '8'])).
% 0.85/1.07  thf('10', plain,
% 0.85/1.07      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.85/1.07        (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))),
% 0.85/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.07  thf('11', plain,
% 0.85/1.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.07         (~ (r2_hidden @ X0 @ X1)
% 0.85/1.07          | (r2_hidden @ X0 @ X2)
% 0.85/1.07          | ~ (r1_tarski @ X1 @ X2))),
% 0.85/1.07      inference('cnf', [status(esa)], [d3_tarski])).
% 0.85/1.07  thf('12', plain,
% 0.85/1.07      (![X0 : $i]:
% 0.85/1.07         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))
% 0.85/1.07          | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.85/1.07      inference('sup-', [status(thm)], ['10', '11'])).
% 0.85/1.07  thf('13', plain,
% 0.85/1.07      (![X0 : $i]:
% 0.85/1.07         ((r1_tarski @ sk_B @ X0)
% 0.85/1.07          | ((k1_xboole_0) = (sk_A))
% 0.85/1.07          | (r2_hidden @ 
% 0.85/1.07             (k4_tarski @ (sk_C_1 @ sk_A @ k1_xboole_0) @ (sk_C @ X0 @ sk_B)) @ 
% 0.85/1.07             (k2_zfmisc_1 @ sk_C_2 @ sk_D_1)))),
% 0.85/1.07      inference('sup-', [status(thm)], ['9', '12'])).
% 0.85/1.07  thf('14', plain,
% 0.85/1.07      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.85/1.07         ((r2_hidden @ X25 @ X26)
% 0.85/1.07          | ~ (r2_hidden @ (k4_tarski @ X23 @ X25) @ (k2_zfmisc_1 @ X24 @ X26)))),
% 0.85/1.07      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.85/1.07  thf('15', plain,
% 0.85/1.07      (![X0 : $i]:
% 0.85/1.07         (((k1_xboole_0) = (sk_A))
% 0.85/1.07          | (r1_tarski @ sk_B @ X0)
% 0.85/1.07          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_D_1))),
% 0.85/1.07      inference('sup-', [status(thm)], ['13', '14'])).
% 0.85/1.07  thf('16', plain,
% 0.85/1.07      (![X1 : $i, X3 : $i]:
% 0.85/1.07         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.85/1.07      inference('cnf', [status(esa)], [d3_tarski])).
% 0.85/1.07  thf('17', plain,
% 0.85/1.07      (((r1_tarski @ sk_B @ sk_D_1)
% 0.85/1.07        | ((k1_xboole_0) = (sk_A))
% 0.85/1.07        | (r1_tarski @ sk_B @ sk_D_1))),
% 0.85/1.07      inference('sup-', [status(thm)], ['15', '16'])).
% 0.85/1.07  thf('18', plain, ((((k1_xboole_0) = (sk_A)) | (r1_tarski @ sk_B @ sk_D_1))),
% 0.85/1.07      inference('simplify', [status(thm)], ['17'])).
% 0.85/1.07  thf('19', plain,
% 0.85/1.07      ((~ (r1_tarski @ sk_A @ sk_C_2) | ~ (r1_tarski @ sk_B @ sk_D_1))),
% 0.85/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.07  thf('20', plain,
% 0.85/1.07      ((~ (r1_tarski @ sk_B @ sk_D_1)) <= (~ ((r1_tarski @ sk_B @ sk_D_1)))),
% 0.85/1.07      inference('split', [status(esa)], ['19'])).
% 0.85/1.07  thf('21', plain,
% 0.85/1.07      (![X1 : $i, X3 : $i]:
% 0.85/1.07         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.85/1.07      inference('cnf', [status(esa)], [d3_tarski])).
% 0.85/1.07  thf('22', plain,
% 0.85/1.07      (![X0 : $i]:
% 0.85/1.07         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.85/1.07          | ((k1_xboole_0) = (X0)))),
% 0.85/1.07      inference('sup-', [status(thm)], ['1', '4'])).
% 0.85/1.07  thf('23', plain,
% 0.85/1.07      (![X23 : $i, X24 : $i, X25 : $i, X27 : $i]:
% 0.85/1.07         ((r2_hidden @ (k4_tarski @ X23 @ X25) @ (k2_zfmisc_1 @ X24 @ X27))
% 0.85/1.07          | ~ (r2_hidden @ X25 @ X27)
% 0.85/1.07          | ~ (r2_hidden @ X23 @ X24))),
% 0.85/1.07      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.85/1.07  thf('24', plain,
% 0.85/1.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.07         (((k1_xboole_0) = (X0))
% 0.85/1.07          | ~ (r2_hidden @ X2 @ X1)
% 0.85/1.07          | (r2_hidden @ (k4_tarski @ X2 @ (sk_C_1 @ X0 @ k1_xboole_0)) @ 
% 0.85/1.07             (k2_zfmisc_1 @ X1 @ X0)))),
% 0.85/1.07      inference('sup-', [status(thm)], ['22', '23'])).
% 0.85/1.07  thf('25', plain,
% 0.85/1.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.07         ((r1_tarski @ X0 @ X1)
% 0.85/1.07          | (r2_hidden @ 
% 0.85/1.07             (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_C_1 @ X2 @ k1_xboole_0)) @ 
% 0.85/1.07             (k2_zfmisc_1 @ X0 @ X2))
% 0.85/1.07          | ((k1_xboole_0) = (X2)))),
% 0.85/1.07      inference('sup-', [status(thm)], ['21', '24'])).
% 0.85/1.07  thf('26', plain,
% 0.85/1.07      (![X0 : $i]:
% 0.85/1.07         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_D_1))
% 0.85/1.07          | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.85/1.07      inference('sup-', [status(thm)], ['10', '11'])).
% 0.85/1.07  thf('27', plain,
% 0.85/1.07      (![X0 : $i]:
% 0.85/1.07         (((k1_xboole_0) = (sk_B))
% 0.85/1.07          | (r1_tarski @ sk_A @ X0)
% 0.85/1.07          | (r2_hidden @ 
% 0.85/1.07             (k4_tarski @ (sk_C @ X0 @ sk_A) @ (sk_C_1 @ sk_B @ k1_xboole_0)) @ 
% 0.85/1.07             (k2_zfmisc_1 @ sk_C_2 @ sk_D_1)))),
% 0.85/1.07      inference('sup-', [status(thm)], ['25', '26'])).
% 0.85/1.07  thf('28', plain,
% 0.85/1.07      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.85/1.07         ((r2_hidden @ X23 @ X24)
% 0.85/1.07          | ~ (r2_hidden @ (k4_tarski @ X23 @ X25) @ (k2_zfmisc_1 @ X24 @ X26)))),
% 0.85/1.07      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.85/1.07  thf('29', plain,
% 0.85/1.07      (![X0 : $i]:
% 0.85/1.07         ((r1_tarski @ sk_A @ X0)
% 0.85/1.07          | ((k1_xboole_0) = (sk_B))
% 0.85/1.07          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_C_2))),
% 0.85/1.07      inference('sup-', [status(thm)], ['27', '28'])).
% 0.85/1.07  thf('30', plain,
% 0.85/1.07      (![X1 : $i, X3 : $i]:
% 0.85/1.07         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.85/1.07      inference('cnf', [status(esa)], [d3_tarski])).
% 0.85/1.07  thf('31', plain,
% 0.85/1.07      ((((k1_xboole_0) = (sk_B))
% 0.85/1.07        | (r1_tarski @ sk_A @ sk_C_2)
% 0.85/1.07        | (r1_tarski @ sk_A @ sk_C_2))),
% 0.85/1.07      inference('sup-', [status(thm)], ['29', '30'])).
% 0.85/1.07  thf('32', plain, (((r1_tarski @ sk_A @ sk_C_2) | ((k1_xboole_0) = (sk_B)))),
% 0.85/1.07      inference('simplify', [status(thm)], ['31'])).
% 0.85/1.07  thf('33', plain,
% 0.85/1.07      ((~ (r1_tarski @ sk_A @ sk_C_2)) <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 0.85/1.07      inference('split', [status(esa)], ['19'])).
% 0.85/1.07  thf('34', plain,
% 0.85/1.07      ((((k1_xboole_0) = (sk_B))) <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 0.85/1.07      inference('sup-', [status(thm)], ['32', '33'])).
% 0.85/1.07  thf('35', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.85/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.07  thf('36', plain,
% 0.85/1.07      ((((k2_zfmisc_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.85/1.07         <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 0.85/1.07      inference('sup-', [status(thm)], ['34', '35'])).
% 0.85/1.07  thf(d2_zfmisc_1, axiom,
% 0.85/1.07    (![A:$i,B:$i,C:$i]:
% 0.85/1.07     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.85/1.07       ( ![D:$i]:
% 0.85/1.07         ( ( r2_hidden @ D @ C ) <=>
% 0.85/1.07           ( ?[E:$i,F:$i]:
% 0.85/1.07             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.85/1.07               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.85/1.07  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.85/1.07  thf(zf_stmt_2, axiom,
% 0.85/1.07    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.85/1.07     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.85/1.07       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.85/1.07         ( r2_hidden @ E @ A ) ) ))).
% 0.85/1.07  thf(zf_stmt_3, axiom,
% 0.85/1.07    (![A:$i,B:$i,C:$i]:
% 0.85/1.07     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.85/1.07       ( ![D:$i]:
% 0.85/1.07         ( ( r2_hidden @ D @ C ) <=>
% 0.85/1.07           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.85/1.07  thf('37', plain,
% 0.85/1.07      (![X16 : $i, X17 : $i, X20 : $i]:
% 0.85/1.07         (((X20) = (k2_zfmisc_1 @ X17 @ X16))
% 0.85/1.07          | (zip_tseitin_0 @ (sk_F @ X20 @ X16 @ X17) @ 
% 0.85/1.07             (sk_E @ X20 @ X16 @ X17) @ (sk_D @ X20 @ X16 @ X17) @ X16 @ X17)
% 0.85/1.07          | (r2_hidden @ (sk_D @ X20 @ X16 @ X17) @ X20))),
% 0.85/1.07      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.85/1.07  thf('38', plain,
% 0.85/1.07      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.85/1.07         ((r2_hidden @ X8 @ X10) | ~ (zip_tseitin_0 @ X8 @ X7 @ X9 @ X10 @ X11))),
% 0.85/1.07      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.85/1.07  thf('39', plain,
% 0.85/1.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.07         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.85/1.07          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.85/1.07          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.85/1.07      inference('sup-', [status(thm)], ['37', '38'])).
% 0.85/1.07  thf('40', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.85/1.07      inference('sup-', [status(thm)], ['2', '3'])).
% 0.85/1.07  thf('41', plain,
% 0.85/1.07      (![X0 : $i, X1 : $i]:
% 0.85/1.07         ((r2_hidden @ (sk_F @ k1_xboole_0 @ X1 @ X0) @ X1)
% 0.85/1.07          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.85/1.07      inference('sup-', [status(thm)], ['39', '40'])).
% 0.85/1.07  thf('42', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.85/1.07      inference('sup-', [status(thm)], ['2', '3'])).
% 0.85/1.07  thf('43', plain,
% 0.85/1.07      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ k1_xboole_0))),
% 0.85/1.07      inference('sup-', [status(thm)], ['41', '42'])).
% 0.85/1.07  thf('44', plain,
% 0.85/1.07      ((((k1_xboole_0) != (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C_2)))),
% 0.85/1.07      inference('demod', [status(thm)], ['36', '43'])).
% 0.85/1.07  thf('45', plain, (((r1_tarski @ sk_A @ sk_C_2))),
% 0.85/1.07      inference('simplify', [status(thm)], ['44'])).
% 0.85/1.07  thf('46', plain,
% 0.85/1.07      (~ ((r1_tarski @ sk_B @ sk_D_1)) | ~ ((r1_tarski @ sk_A @ sk_C_2))),
% 0.85/1.07      inference('split', [status(esa)], ['19'])).
% 0.85/1.07  thf('47', plain, (~ ((r1_tarski @ sk_B @ sk_D_1))),
% 0.85/1.07      inference('sat_resolution*', [status(thm)], ['45', '46'])).
% 0.85/1.07  thf('48', plain, (~ (r1_tarski @ sk_B @ sk_D_1)),
% 0.85/1.07      inference('simpl_trail', [status(thm)], ['20', '47'])).
% 0.85/1.07  thf('49', plain, (((k1_xboole_0) = (sk_A))),
% 0.85/1.07      inference('clc', [status(thm)], ['18', '48'])).
% 0.85/1.07  thf('50', plain,
% 0.85/1.07      (![X16 : $i, X17 : $i, X20 : $i]:
% 0.85/1.07         (((X20) = (k2_zfmisc_1 @ X17 @ X16))
% 0.85/1.07          | (zip_tseitin_0 @ (sk_F @ X20 @ X16 @ X17) @ 
% 0.85/1.07             (sk_E @ X20 @ X16 @ X17) @ (sk_D @ X20 @ X16 @ X17) @ X16 @ X17)
% 0.85/1.07          | (r2_hidden @ (sk_D @ X20 @ X16 @ X17) @ X20))),
% 0.85/1.07      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.85/1.07  thf('51', plain,
% 0.85/1.07      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.85/1.07         ((r2_hidden @ X7 @ X11) | ~ (zip_tseitin_0 @ X8 @ X7 @ X9 @ X10 @ X11))),
% 0.85/1.07      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.85/1.07  thf('52', plain,
% 0.85/1.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.07         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.85/1.07          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.85/1.07          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X0))),
% 0.85/1.07      inference('sup-', [status(thm)], ['50', '51'])).
% 0.85/1.07  thf('53', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.85/1.07      inference('sup-', [status(thm)], ['2', '3'])).
% 0.85/1.07  thf('54', plain,
% 0.85/1.07      (![X0 : $i, X1 : $i]:
% 0.85/1.07         ((r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.85/1.07          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.85/1.07      inference('sup-', [status(thm)], ['52', '53'])).
% 0.85/1.07  thf('55', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.85/1.07      inference('sup-', [status(thm)], ['2', '3'])).
% 0.85/1.07  thf('56', plain,
% 0.85/1.07      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.85/1.07      inference('sup-', [status(thm)], ['54', '55'])).
% 0.85/1.07  thf('57', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.85/1.07      inference('demod', [status(thm)], ['0', '49', '56'])).
% 0.85/1.07  thf('58', plain, ($false), inference('simplify', [status(thm)], ['57'])).
% 0.85/1.07  
% 0.85/1.07  % SZS output end Refutation
% 0.85/1.07  
% 0.95/1.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
