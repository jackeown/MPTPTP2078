%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fA1WZGtLt2

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:02 EST 2020

% Result     : Theorem 0.86s
% Output     : Refutation 0.86s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 187 expanded)
%              Number of leaves         :   31 (  72 expanded)
%              Depth                    :   19
%              Number of atoms          :  632 (1138 expanded)
%              Number of equality atoms :   52 ( 110 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(t46_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t46_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('1',plain,(
    ! [X41: $i,X43: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X41 ) @ X43 )
      | ~ ( r2_hidden @ X41 @ X43 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('2',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

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

thf('7',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C @ X12 @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('8',plain,(
    ! [X41: $i,X43: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X41 ) @ X43 )
      | ~ ( r2_hidden @ X41 @ X43 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('10',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_tarski @ X30 @ X29 )
      = ( k2_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X44 @ X45 ) )
      = ( k2_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X44 @ X45 ) )
      = ( k2_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X20: $i] :
      ( ( k2_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X25: $i,X26: $i] :
      ( r1_tarski @ X25 @ ( k2_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X15: $i,X17: $i] :
      ( ( X15 = X17 )
      | ~ ( r1_tarski @ X17 @ X15 )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( ( k1_tarski @ ( sk_C @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','20'])).

thf('22',plain,(
    ! [X20: $i] :
      ( ( k2_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('23',plain,(
    ! [X25: $i,X26: $i] :
      ( r1_tarski @ X25 @ ( k2_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X41: $i,X42: $i] :
      ( ( r2_hidden @ X41 @ X42 )
      | ~ ( r1_tarski @ ( k1_tarski @ X41 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','28'])).

thf('30',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('32',plain,(
    ! [X25: $i,X26: $i] :
      ( r1_tarski @ X25 @ ( k2_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('33',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('36',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X8 )
      | ( r2_hidden @ X9 @ X7 )
      | ( X8
       != ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('37',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','38'])).

thf('40',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( sk_B @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('45',plain,(
    ! [X41: $i,X43: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X41 ) @ X43 )
      | ~ ( r2_hidden @ X41 @ X43 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('48',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k1_tarski @ ( sk_B @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('50',plain,(
    ! [X25: $i,X26: $i] :
      ( r1_tarski @ X25 @ ( k2_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('51',plain,(
    ! [X41: $i,X42: $i] :
      ( ( r2_hidden @ X41 @ X42 )
      | ~ ( r1_tarski @ ( k1_tarski @ X41 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v1_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v1_xboole_0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','55'])).

thf('57',plain,(
    ! [X20: $i] :
      ( ( k2_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','58'])).

thf('60',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['29','60'])).

thf(t88_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
        = A ) ) )).

thf('62',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X27 @ X28 ) @ X28 )
        = X27 )
      | ~ ( r1_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('67',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','70'])).

thf('72',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['6','71'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('73',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X23 ) )
      = ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('74',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X20: $i] :
      ( ( k2_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('76',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('79',plain,(
    ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
 != sk_B_1 ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['76','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fA1WZGtLt2
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:08:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.86/1.06  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.86/1.06  % Solved by: fo/fo7.sh
% 0.86/1.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.86/1.06  % done 1757 iterations in 0.604s
% 0.86/1.06  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.86/1.06  % SZS output start Refutation
% 0.86/1.06  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.86/1.06  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.86/1.06  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.86/1.06  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.86/1.06  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.86/1.06  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.86/1.06  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.86/1.06  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.86/1.06  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.86/1.06  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.86/1.06  thf(sk_A_type, type, sk_A: $i).
% 0.86/1.06  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.86/1.06  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.86/1.06  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.86/1.06  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.86/1.06  thf(sk_B_type, type, sk_B: $i > $i).
% 0.86/1.06  thf(t46_zfmisc_1, conjecture,
% 0.86/1.06    (![A:$i,B:$i]:
% 0.86/1.06     ( ( r2_hidden @ A @ B ) =>
% 0.86/1.06       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.86/1.06  thf(zf_stmt_0, negated_conjecture,
% 0.86/1.06    (~( ![A:$i,B:$i]:
% 0.86/1.06        ( ( r2_hidden @ A @ B ) =>
% 0.86/1.06          ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ) )),
% 0.86/1.06    inference('cnf.neg', [status(esa)], [t46_zfmisc_1])).
% 0.86/1.06  thf('0', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.86/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.06  thf(l1_zfmisc_1, axiom,
% 0.86/1.06    (![A:$i,B:$i]:
% 0.86/1.06     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.86/1.06  thf('1', plain,
% 0.86/1.06      (![X41 : $i, X43 : $i]:
% 0.86/1.06         ((r1_tarski @ (k1_tarski @ X41) @ X43) | ~ (r2_hidden @ X41 @ X43))),
% 0.86/1.06      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.86/1.06  thf('2', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.86/1.06      inference('sup-', [status(thm)], ['0', '1'])).
% 0.86/1.06  thf(t28_xboole_1, axiom,
% 0.86/1.06    (![A:$i,B:$i]:
% 0.86/1.06     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.86/1.06  thf('3', plain,
% 0.86/1.06      (![X21 : $i, X22 : $i]:
% 0.86/1.06         (((k3_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_tarski @ X21 @ X22))),
% 0.86/1.06      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.86/1.06  thf('4', plain,
% 0.86/1.06      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))),
% 0.86/1.06      inference('sup-', [status(thm)], ['2', '3'])).
% 0.86/1.06  thf(t100_xboole_1, axiom,
% 0.86/1.06    (![A:$i,B:$i]:
% 0.86/1.06     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.86/1.06  thf('5', plain,
% 0.86/1.06      (![X18 : $i, X19 : $i]:
% 0.86/1.06         ((k4_xboole_0 @ X18 @ X19)
% 0.86/1.06           = (k5_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19)))),
% 0.86/1.06      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.86/1.06  thf('6', plain,
% 0.86/1.06      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.86/1.06         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.86/1.06      inference('sup+', [status(thm)], ['4', '5'])).
% 0.86/1.06  thf(t3_xboole_0, axiom,
% 0.86/1.06    (![A:$i,B:$i]:
% 0.86/1.06     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.86/1.06            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.86/1.06       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.86/1.06            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.86/1.06  thf('7', plain,
% 0.86/1.06      (![X11 : $i, X12 : $i]:
% 0.86/1.06         ((r1_xboole_0 @ X11 @ X12) | (r2_hidden @ (sk_C @ X12 @ X11) @ X11))),
% 0.86/1.06      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.86/1.06  thf('8', plain,
% 0.86/1.06      (![X41 : $i, X43 : $i]:
% 0.86/1.06         ((r1_tarski @ (k1_tarski @ X41) @ X43) | ~ (r2_hidden @ X41 @ X43))),
% 0.86/1.06      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.86/1.06  thf('9', plain,
% 0.86/1.06      (![X0 : $i, X1 : $i]:
% 0.86/1.06         ((r1_xboole_0 @ X0 @ X1)
% 0.86/1.06          | (r1_tarski @ (k1_tarski @ (sk_C @ X1 @ X0)) @ X0))),
% 0.86/1.06      inference('sup-', [status(thm)], ['7', '8'])).
% 0.86/1.06  thf(commutativity_k2_tarski, axiom,
% 0.86/1.06    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.86/1.06  thf('10', plain,
% 0.86/1.06      (![X29 : $i, X30 : $i]:
% 0.86/1.06         ((k2_tarski @ X30 @ X29) = (k2_tarski @ X29 @ X30))),
% 0.86/1.06      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.86/1.06  thf(l51_zfmisc_1, axiom,
% 0.86/1.06    (![A:$i,B:$i]:
% 0.86/1.06     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.86/1.06  thf('11', plain,
% 0.86/1.06      (![X44 : $i, X45 : $i]:
% 0.86/1.06         ((k3_tarski @ (k2_tarski @ X44 @ X45)) = (k2_xboole_0 @ X44 @ X45))),
% 0.86/1.06      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.86/1.06  thf('12', plain,
% 0.86/1.06      (![X0 : $i, X1 : $i]:
% 0.86/1.06         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.86/1.06      inference('sup+', [status(thm)], ['10', '11'])).
% 0.86/1.06  thf('13', plain,
% 0.86/1.06      (![X44 : $i, X45 : $i]:
% 0.86/1.06         ((k3_tarski @ (k2_tarski @ X44 @ X45)) = (k2_xboole_0 @ X44 @ X45))),
% 0.86/1.06      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.86/1.06  thf('14', plain,
% 0.86/1.06      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.86/1.06      inference('sup+', [status(thm)], ['12', '13'])).
% 0.86/1.06  thf(t1_boole, axiom,
% 0.86/1.06    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.86/1.06  thf('15', plain, (![X20 : $i]: ((k2_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.86/1.06      inference('cnf', [status(esa)], [t1_boole])).
% 0.86/1.06  thf('16', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.86/1.06      inference('sup+', [status(thm)], ['14', '15'])).
% 0.86/1.06  thf(t7_xboole_1, axiom,
% 0.86/1.06    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.86/1.06  thf('17', plain,
% 0.86/1.06      (![X25 : $i, X26 : $i]: (r1_tarski @ X25 @ (k2_xboole_0 @ X25 @ X26))),
% 0.86/1.06      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.86/1.06  thf('18', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.86/1.06      inference('sup+', [status(thm)], ['16', '17'])).
% 0.86/1.06  thf(d10_xboole_0, axiom,
% 0.86/1.06    (![A:$i,B:$i]:
% 0.86/1.06     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.86/1.06  thf('19', plain,
% 0.86/1.06      (![X15 : $i, X17 : $i]:
% 0.86/1.06         (((X15) = (X17))
% 0.86/1.06          | ~ (r1_tarski @ X17 @ X15)
% 0.86/1.06          | ~ (r1_tarski @ X15 @ X17))),
% 0.86/1.06      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.86/1.06  thf('20', plain,
% 0.86/1.06      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.86/1.06      inference('sup-', [status(thm)], ['18', '19'])).
% 0.86/1.06  thf('21', plain,
% 0.86/1.06      (![X0 : $i]:
% 0.86/1.06         ((r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.86/1.06          | ((k1_tarski @ (sk_C @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.86/1.06      inference('sup-', [status(thm)], ['9', '20'])).
% 0.86/1.06  thf('22', plain, (![X20 : $i]: ((k2_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.86/1.06      inference('cnf', [status(esa)], [t1_boole])).
% 0.86/1.06  thf('23', plain,
% 0.86/1.06      (![X25 : $i, X26 : $i]: (r1_tarski @ X25 @ (k2_xboole_0 @ X25 @ X26))),
% 0.86/1.06      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.86/1.06  thf('24', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.86/1.06      inference('sup+', [status(thm)], ['22', '23'])).
% 0.86/1.06  thf('25', plain,
% 0.86/1.06      (![X41 : $i, X42 : $i]:
% 0.86/1.06         ((r2_hidden @ X41 @ X42) | ~ (r1_tarski @ (k1_tarski @ X41) @ X42))),
% 0.86/1.06      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.86/1.06  thf('26', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.86/1.06      inference('sup-', [status(thm)], ['24', '25'])).
% 0.86/1.06  thf(d1_xboole_0, axiom,
% 0.86/1.06    (![A:$i]:
% 0.86/1.06     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.86/1.06  thf('27', plain,
% 0.86/1.06      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.86/1.06      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.86/1.06  thf('28', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.86/1.06      inference('sup-', [status(thm)], ['26', '27'])).
% 0.86/1.06  thf('29', plain,
% 0.86/1.06      (![X0 : $i]:
% 0.86/1.06         (~ (v1_xboole_0 @ k1_xboole_0) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.86/1.06      inference('sup-', [status(thm)], ['21', '28'])).
% 0.86/1.06  thf('30', plain,
% 0.86/1.06      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.86/1.06      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.86/1.06  thf('31', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.86/1.06      inference('sup+', [status(thm)], ['14', '15'])).
% 0.86/1.06  thf('32', plain,
% 0.86/1.06      (![X25 : $i, X26 : $i]: (r1_tarski @ X25 @ (k2_xboole_0 @ X25 @ X26))),
% 0.86/1.06      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.86/1.06  thf('33', plain,
% 0.86/1.06      (![X21 : $i, X22 : $i]:
% 0.86/1.06         (((k3_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_tarski @ X21 @ X22))),
% 0.86/1.06      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.86/1.06  thf('34', plain,
% 0.86/1.06      (![X0 : $i, X1 : $i]:
% 0.86/1.06         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.86/1.06      inference('sup-', [status(thm)], ['32', '33'])).
% 0.86/1.06  thf('35', plain,
% 0.86/1.06      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.86/1.06      inference('sup+', [status(thm)], ['31', '34'])).
% 0.86/1.06  thf(d4_xboole_0, axiom,
% 0.86/1.06    (![A:$i,B:$i,C:$i]:
% 0.86/1.06     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.86/1.06       ( ![D:$i]:
% 0.86/1.06         ( ( r2_hidden @ D @ C ) <=>
% 0.86/1.06           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.86/1.06  thf('36', plain,
% 0.86/1.06      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.86/1.06         (~ (r2_hidden @ X9 @ X8)
% 0.86/1.06          | (r2_hidden @ X9 @ X7)
% 0.86/1.06          | ((X8) != (k3_xboole_0 @ X6 @ X7)))),
% 0.86/1.06      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.86/1.06  thf('37', plain,
% 0.86/1.06      (![X6 : $i, X7 : $i, X9 : $i]:
% 0.86/1.06         ((r2_hidden @ X9 @ X7) | ~ (r2_hidden @ X9 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.86/1.06      inference('simplify', [status(thm)], ['36'])).
% 0.86/1.06  thf('38', plain,
% 0.86/1.06      (![X0 : $i, X1 : $i]:
% 0.86/1.06         (~ (r2_hidden @ X1 @ k1_xboole_0) | (r2_hidden @ X1 @ X0))),
% 0.86/1.06      inference('sup-', [status(thm)], ['35', '37'])).
% 0.86/1.06  thf('39', plain,
% 0.86/1.06      (![X0 : $i]:
% 0.86/1.06         ((v1_xboole_0 @ k1_xboole_0) | (r2_hidden @ (sk_B @ k1_xboole_0) @ X0))),
% 0.86/1.06      inference('sup-', [status(thm)], ['30', '38'])).
% 0.86/1.06  thf('40', plain,
% 0.86/1.06      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.86/1.06      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.86/1.06  thf(antisymmetry_r2_hidden, axiom,
% 0.86/1.06    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.86/1.06  thf('41', plain,
% 0.86/1.06      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.86/1.06      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.86/1.06  thf('42', plain,
% 0.86/1.06      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r2_hidden @ X0 @ (sk_B @ X0)))),
% 0.86/1.06      inference('sup-', [status(thm)], ['40', '41'])).
% 0.86/1.06  thf('43', plain,
% 0.86/1.06      (((v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ (sk_B @ k1_xboole_0)))),
% 0.86/1.06      inference('sup-', [status(thm)], ['39', '42'])).
% 0.86/1.06  thf('44', plain,
% 0.86/1.06      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.86/1.06      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.86/1.06  thf('45', plain,
% 0.86/1.06      (![X41 : $i, X43 : $i]:
% 0.86/1.06         ((r1_tarski @ (k1_tarski @ X41) @ X43) | ~ (r2_hidden @ X41 @ X43))),
% 0.86/1.06      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.86/1.06  thf('46', plain,
% 0.86/1.06      (![X0 : $i]:
% 0.86/1.06         ((v1_xboole_0 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.86/1.06      inference('sup-', [status(thm)], ['44', '45'])).
% 0.86/1.06  thf('47', plain,
% 0.86/1.06      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.86/1.06      inference('sup-', [status(thm)], ['18', '19'])).
% 0.86/1.06  thf('48', plain,
% 0.86/1.06      (((v1_xboole_0 @ k1_xboole_0)
% 0.86/1.06        | ((k1_tarski @ (sk_B @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.86/1.06      inference('sup-', [status(thm)], ['46', '47'])).
% 0.86/1.06  thf('49', plain,
% 0.86/1.06      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.86/1.06      inference('sup+', [status(thm)], ['12', '13'])).
% 0.86/1.06  thf('50', plain,
% 0.86/1.06      (![X25 : $i, X26 : $i]: (r1_tarski @ X25 @ (k2_xboole_0 @ X25 @ X26))),
% 0.86/1.06      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.86/1.06  thf('51', plain,
% 0.86/1.06      (![X41 : $i, X42 : $i]:
% 0.86/1.06         ((r2_hidden @ X41 @ X42) | ~ (r1_tarski @ (k1_tarski @ X41) @ X42))),
% 0.86/1.06      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.86/1.06  thf('52', plain,
% 0.86/1.06      (![X0 : $i, X1 : $i]:
% 0.86/1.06         (r2_hidden @ X1 @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0))),
% 0.86/1.06      inference('sup-', [status(thm)], ['50', '51'])).
% 0.86/1.06  thf('53', plain,
% 0.86/1.06      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.86/1.06      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.86/1.06  thf('54', plain,
% 0.86/1.06      (![X0 : $i, X1 : $i]:
% 0.86/1.06         ~ (v1_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0))),
% 0.86/1.06      inference('sup-', [status(thm)], ['52', '53'])).
% 0.86/1.06  thf('55', plain,
% 0.86/1.06      (![X0 : $i, X1 : $i]:
% 0.86/1.06         ~ (v1_xboole_0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.86/1.06      inference('sup-', [status(thm)], ['49', '54'])).
% 0.86/1.06  thf('56', plain,
% 0.86/1.06      (![X0 : $i]:
% 0.86/1.06         (~ (v1_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0))
% 0.86/1.06          | (v1_xboole_0 @ k1_xboole_0))),
% 0.86/1.06      inference('sup-', [status(thm)], ['48', '55'])).
% 0.86/1.06  thf('57', plain, (![X20 : $i]: ((k2_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.86/1.06      inference('cnf', [status(esa)], [t1_boole])).
% 0.86/1.06  thf('58', plain,
% 0.86/1.06      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ k1_xboole_0))),
% 0.86/1.06      inference('demod', [status(thm)], ['56', '57'])).
% 0.86/1.06  thf('59', plain,
% 0.86/1.06      (((v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ k1_xboole_0))),
% 0.86/1.06      inference('sup-', [status(thm)], ['43', '58'])).
% 0.86/1.06  thf('60', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.86/1.06      inference('simplify', [status(thm)], ['59'])).
% 0.86/1.06  thf('61', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.86/1.06      inference('demod', [status(thm)], ['29', '60'])).
% 0.86/1.06  thf(t88_xboole_1, axiom,
% 0.86/1.06    (![A:$i,B:$i]:
% 0.86/1.06     ( ( r1_xboole_0 @ A @ B ) =>
% 0.86/1.06       ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( A ) ) ))).
% 0.86/1.06  thf('62', plain,
% 0.86/1.06      (![X27 : $i, X28 : $i]:
% 0.86/1.06         (((k4_xboole_0 @ (k2_xboole_0 @ X27 @ X28) @ X28) = (X27))
% 0.86/1.06          | ~ (r1_xboole_0 @ X27 @ X28))),
% 0.86/1.06      inference('cnf', [status(esa)], [t88_xboole_1])).
% 0.86/1.06  thf('63', plain,
% 0.86/1.06      (![X0 : $i]:
% 0.86/1.06         ((k4_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ X0) = (k1_xboole_0))),
% 0.86/1.06      inference('sup-', [status(thm)], ['61', '62'])).
% 0.86/1.06  thf('64', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.86/1.06      inference('sup+', [status(thm)], ['14', '15'])).
% 0.86/1.06  thf('65', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.86/1.06      inference('demod', [status(thm)], ['63', '64'])).
% 0.86/1.06  thf('66', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.86/1.06      inference('sup+', [status(thm)], ['22', '23'])).
% 0.86/1.06  thf('67', plain,
% 0.86/1.06      (![X21 : $i, X22 : $i]:
% 0.86/1.06         (((k3_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_tarski @ X21 @ X22))),
% 0.86/1.06      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.86/1.06  thf('68', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.86/1.06      inference('sup-', [status(thm)], ['66', '67'])).
% 0.86/1.06  thf('69', plain,
% 0.86/1.06      (![X18 : $i, X19 : $i]:
% 0.86/1.06         ((k4_xboole_0 @ X18 @ X19)
% 0.86/1.06           = (k5_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19)))),
% 0.86/1.06      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.86/1.06  thf('70', plain,
% 0.86/1.06      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.86/1.06      inference('sup+', [status(thm)], ['68', '69'])).
% 0.86/1.06  thf('71', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.86/1.06      inference('demod', [status(thm)], ['65', '70'])).
% 0.86/1.06  thf('72', plain,
% 0.86/1.06      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))),
% 0.86/1.06      inference('demod', [status(thm)], ['6', '71'])).
% 0.86/1.06  thf(t39_xboole_1, axiom,
% 0.86/1.06    (![A:$i,B:$i]:
% 0.86/1.06     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.86/1.06  thf('73', plain,
% 0.86/1.06      (![X23 : $i, X24 : $i]:
% 0.86/1.06         ((k2_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X23))
% 0.86/1.06           = (k2_xboole_0 @ X23 @ X24))),
% 0.86/1.06      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.86/1.06  thf('74', plain,
% 0.86/1.06      (((k2_xboole_0 @ sk_B_1 @ k1_xboole_0)
% 0.86/1.06         = (k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.86/1.06      inference('sup+', [status(thm)], ['72', '73'])).
% 0.86/1.06  thf('75', plain, (![X20 : $i]: ((k2_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.86/1.06      inference('cnf', [status(esa)], [t1_boole])).
% 0.86/1.06  thf('76', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.86/1.06      inference('demod', [status(thm)], ['74', '75'])).
% 0.86/1.06  thf('77', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (sk_B_1))),
% 0.86/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.06  thf('78', plain,
% 0.86/1.06      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.86/1.06      inference('sup+', [status(thm)], ['12', '13'])).
% 0.86/1.06  thf('79', plain, (((k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) != (sk_B_1))),
% 0.86/1.06      inference('demod', [status(thm)], ['77', '78'])).
% 0.86/1.06  thf('80', plain, ($false),
% 0.86/1.06      inference('simplify_reflect-', [status(thm)], ['76', '79'])).
% 0.86/1.06  
% 0.86/1.06  % SZS output end Refutation
% 0.86/1.06  
% 0.86/1.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
