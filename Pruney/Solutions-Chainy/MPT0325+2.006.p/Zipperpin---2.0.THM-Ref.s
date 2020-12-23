%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Zol2X4Nbsp

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:40 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 169 expanded)
%              Number of leaves         :   19 (  55 expanded)
%              Depth                    :   18
%              Number of atoms          :  696 (1691 expanded)
%              Number of equality atoms :   46 (  91 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

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

thf('1',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('4',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X30 @ X32 ) @ ( k3_xboole_0 @ X31 @ X33 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X30 @ X31 ) @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('5',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C_1 ) @ ( k3_xboole_0 @ sk_B @ sk_D_1 ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X7 )
      | ( X9
       != ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('8',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t118_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )).

thf('13',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ X27 @ X28 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X29 @ X27 ) @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X12: $i,X14: $i] :
      ( ( X12 = X14 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = ( k2_zfmisc_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C_1 ) @ ( k3_xboole_0 @ sk_B @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['5','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('19',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ X27 @ X28 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X27 @ X29 ) @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) @ ( k2_zfmisc_1 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C_1 ) @ ( k3_xboole_0 @ sk_B @ sk_D_1 ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('22',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['17','20','21'])).

thf('23',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('24',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('25',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ X27 @ X28 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X27 @ X29 ) @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ ( k2_zfmisc_1 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['22','31'])).

thf(t117_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) )
          | ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) )
        & ~ ( r1_tarski @ B @ C ) ) )).

thf('33',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( X24 = k1_xboole_0 )
      | ( r1_tarski @ X25 @ X26 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X25 @ X24 ) @ ( k2_zfmisc_1 @ X26 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('34',plain,
    ( ( r1_tarski @ sk_A @ sk_C_1 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_1 )
    | ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) @ ( k2_zfmisc_1 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('38',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C_1 ) @ ( k3_xboole_0 @ sk_B @ sk_D_1 ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('39',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( X24 = k1_xboole_0 )
      | ( r1_tarski @ X25 @ X26 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X24 @ X25 ) @ ( k2_zfmisc_1 @ X24 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C_1 ) @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ X0 @ ( k3_xboole_0 @ sk_B @ sk_D_1 ) )
      | ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
      = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('43',plain,(
    ! [X12: $i,X14: $i] :
      ( ( X12 = X14 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
      = k1_xboole_0 )
    | ( sk_B
      = ( k3_xboole_0 @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('47',plain,
    ( ( r1_tarski @ sk_B @ sk_D_1 )
    | ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D_1 )
   <= ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['35'])).

thf('49',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
      = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C_1 ) @ ( k3_xboole_0 @ sk_B @ sk_D_1 ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('51',plain,
    ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_D_1 ) )
      = ( k2_zfmisc_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('52',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k2_zfmisc_1 @ X22 @ X23 )
        = k1_xboole_0 )
      | ( X22 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('53',plain,(
    ! [X23: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X23 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( k1_xboole_0
      = ( k2_zfmisc_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference(demod,[status(thm)],['51','53'])).

thf('55',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    r1_tarski @ sk_B @ sk_D_1 ),
    inference('simplify_reflect-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_1 )
    | ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['35'])).

thf('58',plain,(
    ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['36','58'])).

thf('60',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['34','59'])).

thf('61',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k2_zfmisc_1 @ X22 @ X23 )
        = k1_xboole_0 )
      | ( X23 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('62',plain,(
    ! [X22: $i] :
      ( ( k2_zfmisc_1 @ X22 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','60','62'])).

thf('64',plain,(
    $false ),
    inference(simplify,[status(thm)],['63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Zol2X4Nbsp
% 0.15/0.38  % Computer   : n023.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 12:52:51 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.39  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 0.50/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.50/0.70  % Solved by: fo/fo7.sh
% 0.50/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.70  % done 306 iterations in 0.203s
% 0.50/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.50/0.70  % SZS output start Refutation
% 0.50/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.70  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.50/0.70  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.50/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.50/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.50/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.50/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.50/0.70  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.50/0.70  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.50/0.70  thf(t138_zfmisc_1, conjecture,
% 0.50/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.70     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.50/0.70       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.50/0.70         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 0.50/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.70    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.70        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.50/0.70          ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.50/0.70            ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ) )),
% 0.50/0.70    inference('cnf.neg', [status(esa)], [t138_zfmisc_1])).
% 0.50/0.70  thf('0', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('1', plain,
% 0.50/0.70      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.50/0.70        (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf(t28_xboole_1, axiom,
% 0.50/0.70    (![A:$i,B:$i]:
% 0.50/0.70     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.50/0.70  thf('2', plain,
% 0.50/0.70      (![X17 : $i, X18 : $i]:
% 0.50/0.70         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 0.50/0.70      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.50/0.70  thf('3', plain,
% 0.50/0.70      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.50/0.70         (k2_zfmisc_1 @ sk_C_1 @ sk_D_1)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.50/0.70      inference('sup-', [status(thm)], ['1', '2'])).
% 0.50/0.70  thf(t123_zfmisc_1, axiom,
% 0.50/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.70     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 0.50/0.70       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.50/0.70  thf('4', plain,
% 0.50/0.70      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.50/0.70         ((k2_zfmisc_1 @ (k3_xboole_0 @ X30 @ X32) @ (k3_xboole_0 @ X31 @ X33))
% 0.50/0.70           = (k3_xboole_0 @ (k2_zfmisc_1 @ X30 @ X31) @ 
% 0.50/0.70              (k2_zfmisc_1 @ X32 @ X33)))),
% 0.50/0.70      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.50/0.70  thf('5', plain,
% 0.50/0.70      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C_1) @ 
% 0.50/0.70         (k3_xboole_0 @ sk_B @ sk_D_1)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.50/0.70      inference('demod', [status(thm)], ['3', '4'])).
% 0.50/0.70  thf(d3_tarski, axiom,
% 0.50/0.70    (![A:$i,B:$i]:
% 0.50/0.70     ( ( r1_tarski @ A @ B ) <=>
% 0.50/0.70       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.50/0.70  thf('6', plain,
% 0.50/0.70      (![X3 : $i, X5 : $i]:
% 0.50/0.70         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.50/0.70      inference('cnf', [status(esa)], [d3_tarski])).
% 0.50/0.70  thf(d4_xboole_0, axiom,
% 0.50/0.70    (![A:$i,B:$i,C:$i]:
% 0.50/0.70     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.50/0.70       ( ![D:$i]:
% 0.50/0.70         ( ( r2_hidden @ D @ C ) <=>
% 0.50/0.70           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.50/0.70  thf('7', plain,
% 0.50/0.70      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.50/0.70         (~ (r2_hidden @ X10 @ X9)
% 0.50/0.70          | (r2_hidden @ X10 @ X7)
% 0.50/0.70          | ((X9) != (k3_xboole_0 @ X7 @ X8)))),
% 0.50/0.70      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.50/0.70  thf('8', plain,
% 0.50/0.70      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.50/0.70         ((r2_hidden @ X10 @ X7)
% 0.50/0.70          | ~ (r2_hidden @ X10 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.50/0.70      inference('simplify', [status(thm)], ['7'])).
% 0.50/0.70  thf('9', plain,
% 0.50/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.70         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.50/0.70          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 0.50/0.70      inference('sup-', [status(thm)], ['6', '8'])).
% 0.50/0.70  thf('10', plain,
% 0.50/0.70      (![X3 : $i, X5 : $i]:
% 0.50/0.70         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.50/0.70      inference('cnf', [status(esa)], [d3_tarski])).
% 0.50/0.70  thf('11', plain,
% 0.50/0.70      (![X0 : $i, X1 : $i]:
% 0.50/0.70         ((r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 0.50/0.70          | (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.50/0.70      inference('sup-', [status(thm)], ['9', '10'])).
% 0.50/0.70  thf('12', plain,
% 0.50/0.70      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.50/0.70      inference('simplify', [status(thm)], ['11'])).
% 0.50/0.70  thf(t118_zfmisc_1, axiom,
% 0.50/0.70    (![A:$i,B:$i,C:$i]:
% 0.50/0.70     ( ( r1_tarski @ A @ B ) =>
% 0.50/0.70       ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.50/0.70         ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 0.50/0.70  thf('13', plain,
% 0.50/0.70      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.50/0.70         (~ (r1_tarski @ X27 @ X28)
% 0.50/0.70          | (r1_tarski @ (k2_zfmisc_1 @ X29 @ X27) @ (k2_zfmisc_1 @ X29 @ X28)))),
% 0.50/0.70      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 0.50/0.70  thf('14', plain,
% 0.50/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.70         (r1_tarski @ (k2_zfmisc_1 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.50/0.70          (k2_zfmisc_1 @ X2 @ X0))),
% 0.50/0.70      inference('sup-', [status(thm)], ['12', '13'])).
% 0.50/0.70  thf(d10_xboole_0, axiom,
% 0.50/0.70    (![A:$i,B:$i]:
% 0.50/0.70     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.50/0.70  thf('15', plain,
% 0.50/0.70      (![X12 : $i, X14 : $i]:
% 0.50/0.70         (((X12) = (X14))
% 0.50/0.70          | ~ (r1_tarski @ X14 @ X12)
% 0.50/0.70          | ~ (r1_tarski @ X12 @ X14))),
% 0.50/0.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.50/0.70  thf('16', plain,
% 0.50/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.70         (~ (r1_tarski @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 0.50/0.70             (k2_zfmisc_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)))
% 0.50/0.70          | ((k2_zfmisc_1 @ X1 @ X0)
% 0.50/0.70              = (k2_zfmisc_1 @ X1 @ (k3_xboole_0 @ X0 @ X2))))),
% 0.50/0.70      inference('sup-', [status(thm)], ['14', '15'])).
% 0.50/0.70  thf('17', plain,
% 0.50/0.70      ((~ (r1_tarski @ (k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C_1) @ sk_B) @ 
% 0.50/0.70           (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.50/0.70        | ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C_1) @ sk_B)
% 0.50/0.70            = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C_1) @ 
% 0.50/0.70               (k3_xboole_0 @ sk_B @ sk_D_1))))),
% 0.50/0.70      inference('sup-', [status(thm)], ['5', '16'])).
% 0.50/0.70  thf('18', plain,
% 0.50/0.70      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.50/0.70      inference('simplify', [status(thm)], ['11'])).
% 0.50/0.70  thf('19', plain,
% 0.50/0.70      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.50/0.70         (~ (r1_tarski @ X27 @ X28)
% 0.50/0.70          | (r1_tarski @ (k2_zfmisc_1 @ X27 @ X29) @ (k2_zfmisc_1 @ X28 @ X29)))),
% 0.50/0.70      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 0.50/0.70  thf('20', plain,
% 0.50/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.70         (r1_tarski @ (k2_zfmisc_1 @ (k3_xboole_0 @ X0 @ X1) @ X2) @ 
% 0.50/0.70          (k2_zfmisc_1 @ X0 @ X2))),
% 0.50/0.70      inference('sup-', [status(thm)], ['18', '19'])).
% 0.50/0.70  thf('21', plain,
% 0.50/0.70      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C_1) @ 
% 0.50/0.70         (k3_xboole_0 @ sk_B @ sk_D_1)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.50/0.70      inference('demod', [status(thm)], ['3', '4'])).
% 0.50/0.70  thf('22', plain,
% 0.50/0.70      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C_1) @ sk_B)
% 0.50/0.70         = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.50/0.70      inference('demod', [status(thm)], ['17', '20', '21'])).
% 0.50/0.70  thf('23', plain,
% 0.50/0.70      (![X3 : $i, X5 : $i]:
% 0.50/0.70         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.50/0.70      inference('cnf', [status(esa)], [d3_tarski])).
% 0.50/0.70  thf('24', plain,
% 0.50/0.70      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.50/0.70         (~ (r2_hidden @ X10 @ X9)
% 0.50/0.70          | (r2_hidden @ X10 @ X8)
% 0.50/0.70          | ((X9) != (k3_xboole_0 @ X7 @ X8)))),
% 0.50/0.70      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.50/0.70  thf('25', plain,
% 0.50/0.70      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.50/0.70         ((r2_hidden @ X10 @ X8)
% 0.50/0.70          | ~ (r2_hidden @ X10 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.50/0.70      inference('simplify', [status(thm)], ['24'])).
% 0.50/0.70  thf('26', plain,
% 0.50/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.70         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.50/0.70          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.50/0.70      inference('sup-', [status(thm)], ['23', '25'])).
% 0.50/0.70  thf('27', plain,
% 0.50/0.70      (![X3 : $i, X5 : $i]:
% 0.50/0.70         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.50/0.70      inference('cnf', [status(esa)], [d3_tarski])).
% 0.50/0.70  thf('28', plain,
% 0.50/0.70      (![X0 : $i, X1 : $i]:
% 0.50/0.70         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.50/0.70          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.50/0.70      inference('sup-', [status(thm)], ['26', '27'])).
% 0.50/0.70  thf('29', plain,
% 0.50/0.70      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.50/0.70      inference('simplify', [status(thm)], ['28'])).
% 0.50/0.70  thf('30', plain,
% 0.50/0.70      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.50/0.70         (~ (r1_tarski @ X27 @ X28)
% 0.50/0.70          | (r1_tarski @ (k2_zfmisc_1 @ X27 @ X29) @ (k2_zfmisc_1 @ X28 @ X29)))),
% 0.50/0.70      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 0.50/0.70  thf('31', plain,
% 0.50/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.70         (r1_tarski @ (k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ X0) @ X2) @ 
% 0.50/0.70          (k2_zfmisc_1 @ X0 @ X2))),
% 0.50/0.70      inference('sup-', [status(thm)], ['29', '30'])).
% 0.50/0.70  thf('32', plain,
% 0.50/0.70      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_C_1 @ sk_B))),
% 0.50/0.70      inference('sup+', [status(thm)], ['22', '31'])).
% 0.50/0.70  thf(t117_zfmisc_1, axiom,
% 0.50/0.70    (![A:$i,B:$i,C:$i]:
% 0.50/0.70     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.50/0.70          ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) ) | 
% 0.50/0.70            ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 0.50/0.70          ( ~( r1_tarski @ B @ C ) ) ) ))).
% 0.50/0.70  thf('33', plain,
% 0.50/0.70      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.50/0.70         (((X24) = (k1_xboole_0))
% 0.50/0.70          | (r1_tarski @ X25 @ X26)
% 0.50/0.70          | ~ (r1_tarski @ (k2_zfmisc_1 @ X25 @ X24) @ 
% 0.50/0.70               (k2_zfmisc_1 @ X26 @ X24)))),
% 0.50/0.70      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 0.50/0.70  thf('34', plain, (((r1_tarski @ sk_A @ sk_C_1) | ((sk_B) = (k1_xboole_0)))),
% 0.50/0.70      inference('sup-', [status(thm)], ['32', '33'])).
% 0.50/0.70  thf('35', plain,
% 0.50/0.70      ((~ (r1_tarski @ sk_A @ sk_C_1) | ~ (r1_tarski @ sk_B @ sk_D_1))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('36', plain,
% 0.50/0.70      ((~ (r1_tarski @ sk_A @ sk_C_1)) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 0.50/0.70      inference('split', [status(esa)], ['35'])).
% 0.50/0.70  thf('37', plain,
% 0.50/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.70         (r1_tarski @ (k2_zfmisc_1 @ (k3_xboole_0 @ X0 @ X1) @ X2) @ 
% 0.50/0.70          (k2_zfmisc_1 @ X0 @ X2))),
% 0.50/0.70      inference('sup-', [status(thm)], ['18', '19'])).
% 0.50/0.70  thf('38', plain,
% 0.50/0.70      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C_1) @ 
% 0.50/0.70         (k3_xboole_0 @ sk_B @ sk_D_1)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.50/0.70      inference('demod', [status(thm)], ['3', '4'])).
% 0.50/0.70  thf('39', plain,
% 0.50/0.70      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.50/0.70         (((X24) = (k1_xboole_0))
% 0.50/0.70          | (r1_tarski @ X25 @ X26)
% 0.50/0.70          | ~ (r1_tarski @ (k2_zfmisc_1 @ X24 @ X25) @ 
% 0.50/0.70               (k2_zfmisc_1 @ X24 @ X26)))),
% 0.50/0.70      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 0.50/0.70  thf('40', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         (~ (r1_tarski @ (k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C_1) @ X0) @ 
% 0.50/0.70             (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.50/0.70          | (r1_tarski @ X0 @ (k3_xboole_0 @ sk_B @ sk_D_1))
% 0.50/0.70          | ((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0)))),
% 0.50/0.70      inference('sup-', [status(thm)], ['38', '39'])).
% 0.50/0.70  thf('41', plain,
% 0.50/0.70      ((((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))
% 0.50/0.70        | (r1_tarski @ sk_B @ (k3_xboole_0 @ sk_B @ sk_D_1)))),
% 0.50/0.70      inference('sup-', [status(thm)], ['37', '40'])).
% 0.50/0.70  thf('42', plain,
% 0.50/0.70      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.50/0.70      inference('simplify', [status(thm)], ['11'])).
% 0.50/0.70  thf('43', plain,
% 0.50/0.70      (![X12 : $i, X14 : $i]:
% 0.50/0.70         (((X12) = (X14))
% 0.50/0.70          | ~ (r1_tarski @ X14 @ X12)
% 0.50/0.70          | ~ (r1_tarski @ X12 @ X14))),
% 0.50/0.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.50/0.70  thf('44', plain,
% 0.50/0.70      (![X0 : $i, X1 : $i]:
% 0.50/0.70         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.50/0.70          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.50/0.70      inference('sup-', [status(thm)], ['42', '43'])).
% 0.50/0.70  thf('45', plain,
% 0.50/0.70      ((((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))
% 0.50/0.70        | ((sk_B) = (k3_xboole_0 @ sk_B @ sk_D_1)))),
% 0.50/0.70      inference('sup-', [status(thm)], ['41', '44'])).
% 0.50/0.70  thf('46', plain,
% 0.50/0.70      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.50/0.70      inference('simplify', [status(thm)], ['28'])).
% 0.50/0.70  thf('47', plain,
% 0.50/0.70      (((r1_tarski @ sk_B @ sk_D_1)
% 0.50/0.70        | ((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0)))),
% 0.50/0.70      inference('sup+', [status(thm)], ['45', '46'])).
% 0.50/0.70  thf('48', plain,
% 0.50/0.70      ((~ (r1_tarski @ sk_B @ sk_D_1)) <= (~ ((r1_tarski @ sk_B @ sk_D_1)))),
% 0.50/0.70      inference('split', [status(esa)], ['35'])).
% 0.50/0.70  thf('49', plain,
% 0.50/0.70      ((((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0)))
% 0.50/0.70         <= (~ ((r1_tarski @ sk_B @ sk_D_1)))),
% 0.50/0.70      inference('sup-', [status(thm)], ['47', '48'])).
% 0.50/0.70  thf('50', plain,
% 0.50/0.70      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C_1) @ 
% 0.50/0.70         (k3_xboole_0 @ sk_B @ sk_D_1)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.50/0.70      inference('demod', [status(thm)], ['3', '4'])).
% 0.50/0.70  thf('51', plain,
% 0.50/0.70      ((((k2_zfmisc_1 @ k1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_D_1))
% 0.50/0.70          = (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.50/0.70         <= (~ ((r1_tarski @ sk_B @ sk_D_1)))),
% 0.50/0.70      inference('sup+', [status(thm)], ['49', '50'])).
% 0.50/0.70  thf(t113_zfmisc_1, axiom,
% 0.50/0.70    (![A:$i,B:$i]:
% 0.50/0.70     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.50/0.70       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.50/0.70  thf('52', plain,
% 0.50/0.70      (![X22 : $i, X23 : $i]:
% 0.50/0.70         (((k2_zfmisc_1 @ X22 @ X23) = (k1_xboole_0))
% 0.50/0.70          | ((X22) != (k1_xboole_0)))),
% 0.50/0.70      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.50/0.70  thf('53', plain,
% 0.50/0.70      (![X23 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X23) = (k1_xboole_0))),
% 0.50/0.70      inference('simplify', [status(thm)], ['52'])).
% 0.50/0.70  thf('54', plain,
% 0.50/0.70      ((((k1_xboole_0) = (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.50/0.70         <= (~ ((r1_tarski @ sk_B @ sk_D_1)))),
% 0.50/0.70      inference('demod', [status(thm)], ['51', '53'])).
% 0.50/0.70  thf('55', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('56', plain, (((r1_tarski @ sk_B @ sk_D_1))),
% 0.50/0.70      inference('simplify_reflect-', [status(thm)], ['54', '55'])).
% 0.50/0.70  thf('57', plain,
% 0.50/0.70      (~ ((r1_tarski @ sk_A @ sk_C_1)) | ~ ((r1_tarski @ sk_B @ sk_D_1))),
% 0.50/0.70      inference('split', [status(esa)], ['35'])).
% 0.50/0.70  thf('58', plain, (~ ((r1_tarski @ sk_A @ sk_C_1))),
% 0.50/0.70      inference('sat_resolution*', [status(thm)], ['56', '57'])).
% 0.50/0.70  thf('59', plain, (~ (r1_tarski @ sk_A @ sk_C_1)),
% 0.50/0.70      inference('simpl_trail', [status(thm)], ['36', '58'])).
% 0.50/0.70  thf('60', plain, (((sk_B) = (k1_xboole_0))),
% 0.50/0.70      inference('clc', [status(thm)], ['34', '59'])).
% 0.50/0.70  thf('61', plain,
% 0.50/0.70      (![X22 : $i, X23 : $i]:
% 0.50/0.70         (((k2_zfmisc_1 @ X22 @ X23) = (k1_xboole_0))
% 0.50/0.70          | ((X23) != (k1_xboole_0)))),
% 0.50/0.70      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.50/0.70  thf('62', plain,
% 0.50/0.70      (![X22 : $i]: ((k2_zfmisc_1 @ X22 @ k1_xboole_0) = (k1_xboole_0))),
% 0.50/0.70      inference('simplify', [status(thm)], ['61'])).
% 0.50/0.70  thf('63', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.50/0.70      inference('demod', [status(thm)], ['0', '60', '62'])).
% 0.50/0.70  thf('64', plain, ($false), inference('simplify', [status(thm)], ['63'])).
% 0.50/0.70  
% 0.50/0.70  % SZS output end Refutation
% 0.50/0.70  
% 0.50/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
