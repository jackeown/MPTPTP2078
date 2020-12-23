%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.u63l3B3vk5

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:45 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 256 expanded)
%              Number of leaves         :   33 (  93 expanded)
%              Depth                    :   19
%              Number of atoms          :  803 (1916 expanded)
%              Number of equality atoms :   94 ( 241 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X61: $i,X62: $i] :
      ( ~ ( v1_relat_1 @ X61 )
      | ~ ( v1_relat_1 @ X62 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X61 @ X62 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t47_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X66: $i,X67: $i] :
      ( ~ ( v1_relat_1 @ X66 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X66 @ X67 ) )
        = ( k2_relat_1 @ X67 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X67 ) @ ( k2_relat_1 @ X66 ) )
      | ~ ( v1_relat_1 @ X67 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('4',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('5',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('7',plain,(
    ! [X58: $i] :
      ( ( v1_relat_1 @ X58 )
      | ( r2_hidden @ ( sk_B @ X58 ) @ X58 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('8',plain,(
    ! [X38: $i,X40: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X38 ) @ X40 )
      | ~ ( r2_hidden @ X38 @ X40 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('10',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('11',plain,
    ( ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k1_tarski @ ( sk_B @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('12',plain,(
    ! [X51: $i,X52: $i] :
      ( ( X52 != X51 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X52 ) @ ( k1_tarski @ X51 ) )
       != ( k1_tarski @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('13',plain,(
    ! [X51: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X51 ) @ ( k1_tarski @ X51 ) )
     != ( k1_tarski @ X51 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X51: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ X51 ) @ ( k1_tarski @ X51 ) )
     != ( k1_tarski @ X51 ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('18',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('19',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k3_xboole_0 @ X3 @ ( k2_xboole_0 @ X3 @ X4 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('20',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X51: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X51 ) ) ),
    inference(demod,[status(thm)],['17','22'])).

thf('24',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['11','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','24'])).

thf(t22_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('26',plain,(
    ! [X63: $i] :
      ( ( ( k3_xboole_0 @ X63 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X63 ) @ ( k2_relat_1 @ X63 ) ) )
        = X63 )
      | ~ ( v1_relat_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) )
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t125_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('30',plain,(
    ! [X47: $i,X49: $i,X50: $i] :
      ( ( k2_zfmisc_1 @ X50 @ ( k4_xboole_0 @ X47 @ X49 ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X50 @ X47 ) @ ( k2_zfmisc_1 @ X50 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('33',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','34'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('36',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['27','35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','37'])).

thf('39',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['11','23'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf(t62_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
          = k1_xboole_0 )
        & ( ( k5_relat_1 @ A @ k1_xboole_0 )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
            = k1_xboole_0 )
          & ( ( k5_relat_1 @ A @ k1_xboole_0 )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_relat_1])).

thf('42',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['42'])).

thf('44',plain,(
    ! [X61: $i,X62: $i] :
      ( ~ ( v1_relat_1 @ X61 )
      | ~ ( v1_relat_1 @ X62 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X61 @ X62 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('45',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t46_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('46',plain,(
    ! [X64: $i,X65: $i] :
      ( ~ ( v1_relat_1 @ X64 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X65 @ X64 ) )
        = ( k1_relat_1 @ X65 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X65 ) @ ( k1_relat_1 @ X64 ) )
      | ~ ( v1_relat_1 @ X65 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('49',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['11','23'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X63: $i] :
      ( ( ( k3_xboole_0 @ X63 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X63 ) @ ( k2_relat_1 @ X63 ) ) )
        = X63 )
      | ~ ( v1_relat_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) )
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('57',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X47 @ X49 ) @ X48 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X47 @ X48 ) @ ( k2_zfmisc_1 @ X49 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('60',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['55','61'])).

thf('63',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['54','62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','64'])).

thf('66',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['11','23'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['42'])).

thf('70',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['42'])).

thf('75',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['73','74'])).

thf('76',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['43','75'])).

thf('77',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    $false ),
    inference(simplify,[status(thm)],['79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.u63l3B3vk5
% 0.13/0.36  % Computer   : n024.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 18:46:36 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.22/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.54  % Solved by: fo/fo7.sh
% 0.22/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.54  % done 112 iterations in 0.060s
% 0.22/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.54  % SZS output start Refutation
% 0.22/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.54  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.22/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.54  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.54  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.54  thf(dt_k5_relat_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.22/0.54       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.22/0.54  thf('0', plain,
% 0.22/0.54      (![X61 : $i, X62 : $i]:
% 0.22/0.54         (~ (v1_relat_1 @ X61)
% 0.22/0.54          | ~ (v1_relat_1 @ X62)
% 0.22/0.54          | (v1_relat_1 @ (k5_relat_1 @ X61 @ X62)))),
% 0.22/0.54      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.22/0.54  thf(t60_relat_1, axiom,
% 0.22/0.54    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.22/0.54     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.54  thf('1', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.54  thf(t47_relat_1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( v1_relat_1 @ A ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( v1_relat_1 @ B ) =>
% 0.22/0.54           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.22/0.54             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.22/0.54  thf('2', plain,
% 0.22/0.54      (![X66 : $i, X67 : $i]:
% 0.22/0.54         (~ (v1_relat_1 @ X66)
% 0.22/0.54          | ((k2_relat_1 @ (k5_relat_1 @ X66 @ X67)) = (k2_relat_1 @ X67))
% 0.22/0.54          | ~ (r1_tarski @ (k1_relat_1 @ X67) @ (k2_relat_1 @ X66))
% 0.22/0.54          | ~ (v1_relat_1 @ X67))),
% 0.22/0.54      inference('cnf', [status(esa)], [t47_relat_1])).
% 0.22/0.54  thf('3', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (r1_tarski @ k1_xboole_0 @ (k2_relat_1 @ X0))
% 0.22/0.54          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.54          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.22/0.54              = (k2_relat_1 @ k1_xboole_0))
% 0.22/0.54          | ~ (v1_relat_1 @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.54  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.54  thf('4', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.22/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.54  thf('5', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.54  thf('6', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.54          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))
% 0.22/0.54          | ~ (v1_relat_1 @ X0))),
% 0.22/0.54      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.22/0.54  thf(d1_relat_1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( v1_relat_1 @ A ) <=>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ~( ( r2_hidden @ B @ A ) & 
% 0.22/0.54              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.22/0.54  thf('7', plain,
% 0.22/0.54      (![X58 : $i]: ((v1_relat_1 @ X58) | (r2_hidden @ (sk_B @ X58) @ X58))),
% 0.22/0.54      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.22/0.54  thf(l1_zfmisc_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.22/0.54  thf('8', plain,
% 0.22/0.54      (![X38 : $i, X40 : $i]:
% 0.22/0.54         ((r1_tarski @ (k1_tarski @ X38) @ X40) | ~ (r2_hidden @ X38 @ X40))),
% 0.22/0.54      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.22/0.54  thf('9', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((v1_relat_1 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.54  thf(t3_xboole_1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.54  thf('10', plain,
% 0.22/0.54      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ k1_xboole_0))),
% 0.22/0.54      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.22/0.54  thf('11', plain,
% 0.22/0.54      (((v1_relat_1 @ k1_xboole_0)
% 0.22/0.54        | ((k1_tarski @ (sk_B @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.54  thf(t20_zfmisc_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.22/0.54         ( k1_tarski @ A ) ) <=>
% 0.22/0.54       ( ( A ) != ( B ) ) ))).
% 0.22/0.54  thf('12', plain,
% 0.22/0.54      (![X51 : $i, X52 : $i]:
% 0.22/0.54         (((X52) != (X51))
% 0.22/0.54          | ((k4_xboole_0 @ (k1_tarski @ X52) @ (k1_tarski @ X51))
% 0.22/0.54              != (k1_tarski @ X52)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.22/0.54  thf('13', plain,
% 0.22/0.54      (![X51 : $i]:
% 0.22/0.54         ((k4_xboole_0 @ (k1_tarski @ X51) @ (k1_tarski @ X51))
% 0.22/0.54           != (k1_tarski @ X51))),
% 0.22/0.54      inference('simplify', [status(thm)], ['12'])).
% 0.22/0.54  thf(idempotence_k3_xboole_0, axiom,
% 0.22/0.54    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.22/0.54  thf('14', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.22/0.54      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.22/0.54  thf(t100_xboole_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.54  thf('15', plain,
% 0.22/0.54      (![X1 : $i, X2 : $i]:
% 0.22/0.54         ((k4_xboole_0 @ X1 @ X2)
% 0.22/0.54           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.54  thf('16', plain,
% 0.22/0.54      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.54      inference('sup+', [status(thm)], ['14', '15'])).
% 0.22/0.54  thf('17', plain,
% 0.22/0.54      (![X51 : $i]:
% 0.22/0.54         ((k5_xboole_0 @ (k1_tarski @ X51) @ (k1_tarski @ X51))
% 0.22/0.54           != (k1_tarski @ X51))),
% 0.22/0.54      inference('demod', [status(thm)], ['13', '16'])).
% 0.22/0.54  thf(t46_xboole_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.22/0.54  thf('18', plain,
% 0.22/0.54      (![X8 : $i, X9 : $i]:
% 0.22/0.54         ((k4_xboole_0 @ X8 @ (k2_xboole_0 @ X8 @ X9)) = (k1_xboole_0))),
% 0.22/0.54      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.22/0.54  thf(t21_xboole_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.22/0.54  thf('19', plain,
% 0.22/0.54      (![X3 : $i, X4 : $i]:
% 0.22/0.54         ((k3_xboole_0 @ X3 @ (k2_xboole_0 @ X3 @ X4)) = (X3))),
% 0.22/0.54      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.22/0.54  thf('20', plain,
% 0.22/0.54      (![X1 : $i, X2 : $i]:
% 0.22/0.54         ((k4_xboole_0 @ X1 @ X2)
% 0.22/0.54           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.54  thf('21', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.22/0.54           = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.54      inference('sup+', [status(thm)], ['19', '20'])).
% 0.22/0.54  thf('22', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.54      inference('sup+', [status(thm)], ['18', '21'])).
% 0.22/0.54  thf('23', plain, (![X51 : $i]: ((k1_xboole_0) != (k1_tarski @ X51))),
% 0.22/0.54      inference('demod', [status(thm)], ['17', '22'])).
% 0.22/0.54  thf('24', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.54      inference('clc', [status(thm)], ['11', '23'])).
% 0.22/0.54  thf('25', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))
% 0.22/0.54          | ~ (v1_relat_1 @ X0))),
% 0.22/0.54      inference('demod', [status(thm)], ['6', '24'])).
% 0.22/0.54  thf(t22_relat_1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( v1_relat_1 @ A ) =>
% 0.22/0.54       ( ( k3_xboole_0 @
% 0.22/0.54           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 0.22/0.54         ( A ) ) ))).
% 0.22/0.54  thf('26', plain,
% 0.22/0.54      (![X63 : $i]:
% 0.22/0.54         (((k3_xboole_0 @ X63 @ 
% 0.22/0.54            (k2_zfmisc_1 @ (k1_relat_1 @ X63) @ (k2_relat_1 @ X63))) = (
% 0.22/0.54            X63))
% 0.22/0.54          | ~ (v1_relat_1 @ X63))),
% 0.22/0.54      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.22/0.54  thf('27', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (((k3_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0) @ 
% 0.22/0.54            (k2_zfmisc_1 @ (k1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.22/0.54             k1_xboole_0))
% 0.22/0.54            = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.22/0.54          | ~ (v1_relat_1 @ X0)
% 0.22/0.54          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.22/0.54      inference('sup+', [status(thm)], ['25', '26'])).
% 0.22/0.54  thf('28', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.54      inference('sup+', [status(thm)], ['18', '21'])).
% 0.22/0.54  thf('29', plain,
% 0.22/0.54      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.54      inference('sup+', [status(thm)], ['14', '15'])).
% 0.22/0.54  thf(t125_zfmisc_1, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) ) =
% 0.22/0.54         ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.22/0.54       ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.22/0.54         ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.22/0.54  thf('30', plain,
% 0.22/0.54      (![X47 : $i, X49 : $i, X50 : $i]:
% 0.22/0.54         ((k2_zfmisc_1 @ X50 @ (k4_xboole_0 @ X47 @ X49))
% 0.22/0.54           = (k4_xboole_0 @ (k2_zfmisc_1 @ X50 @ X47) @ 
% 0.22/0.54              (k2_zfmisc_1 @ X50 @ X49)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.22/0.54  thf('31', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((k2_zfmisc_1 @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.22/0.54           = (k5_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.22/0.54      inference('sup+', [status(thm)], ['29', '30'])).
% 0.22/0.54  thf('32', plain,
% 0.22/0.54      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.54      inference('sup+', [status(thm)], ['14', '15'])).
% 0.22/0.54  thf('33', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.54      inference('sup+', [status(thm)], ['18', '21'])).
% 0.22/0.54  thf('34', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((k2_zfmisc_1 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.22/0.54      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.22/0.54  thf('35', plain,
% 0.22/0.54      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.54      inference('sup+', [status(thm)], ['28', '34'])).
% 0.22/0.54  thf(t2_boole, axiom,
% 0.22/0.54    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.54  thf('36', plain,
% 0.22/0.54      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.54      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.54  thf('37', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.22/0.54          | ~ (v1_relat_1 @ X0)
% 0.22/0.54          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.22/0.54      inference('demod', [status(thm)], ['27', '35', '36'])).
% 0.22/0.54  thf('38', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.54          | ~ (v1_relat_1 @ X0)
% 0.22/0.54          | ~ (v1_relat_1 @ X0)
% 0.22/0.54          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['0', '37'])).
% 0.22/0.54  thf('39', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.54      inference('clc', [status(thm)], ['11', '23'])).
% 0.22/0.54  thf('40', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (v1_relat_1 @ X0)
% 0.22/0.54          | ~ (v1_relat_1 @ X0)
% 0.22/0.54          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.22/0.54      inference('demod', [status(thm)], ['38', '39'])).
% 0.22/0.54  thf('41', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.22/0.54          | ~ (v1_relat_1 @ X0))),
% 0.22/0.54      inference('simplify', [status(thm)], ['40'])).
% 0.22/0.54  thf(t62_relat_1, conjecture,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( v1_relat_1 @ A ) =>
% 0.22/0.54       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.22/0.54         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.54    (~( ![A:$i]:
% 0.22/0.54        ( ( v1_relat_1 @ A ) =>
% 0.22/0.54          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.22/0.54            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.22/0.54    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.22/0.54  thf('42', plain,
% 0.22/0.54      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.22/0.54        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('43', plain,
% 0.22/0.54      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.22/0.54         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.22/0.54      inference('split', [status(esa)], ['42'])).
% 0.22/0.54  thf('44', plain,
% 0.22/0.54      (![X61 : $i, X62 : $i]:
% 0.22/0.54         (~ (v1_relat_1 @ X61)
% 0.22/0.54          | ~ (v1_relat_1 @ X62)
% 0.22/0.54          | (v1_relat_1 @ (k5_relat_1 @ X61 @ X62)))),
% 0.22/0.54      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.22/0.54  thf('45', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.54  thf(t46_relat_1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( v1_relat_1 @ A ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( v1_relat_1 @ B ) =>
% 0.22/0.54           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.22/0.54             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.22/0.54  thf('46', plain,
% 0.22/0.54      (![X64 : $i, X65 : $i]:
% 0.22/0.54         (~ (v1_relat_1 @ X64)
% 0.22/0.54          | ((k1_relat_1 @ (k5_relat_1 @ X65 @ X64)) = (k1_relat_1 @ X65))
% 0.22/0.54          | ~ (r1_tarski @ (k2_relat_1 @ X65) @ (k1_relat_1 @ X64))
% 0.22/0.54          | ~ (v1_relat_1 @ X65))),
% 0.22/0.54      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.22/0.54  thf('47', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.22/0.54          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.54          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.22/0.54              = (k1_relat_1 @ k1_xboole_0))
% 0.22/0.54          | ~ (v1_relat_1 @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['45', '46'])).
% 0.22/0.54  thf('48', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.22/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.54  thf('49', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.54  thf('50', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.54          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.22/0.54          | ~ (v1_relat_1 @ X0))),
% 0.22/0.54      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.22/0.54  thf('51', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.54      inference('clc', [status(thm)], ['11', '23'])).
% 0.22/0.54  thf('52', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.22/0.54          | ~ (v1_relat_1 @ X0))),
% 0.22/0.54      inference('demod', [status(thm)], ['50', '51'])).
% 0.22/0.54  thf('53', plain,
% 0.22/0.54      (![X63 : $i]:
% 0.22/0.54         (((k3_xboole_0 @ X63 @ 
% 0.22/0.54            (k2_zfmisc_1 @ (k1_relat_1 @ X63) @ (k2_relat_1 @ X63))) = (
% 0.22/0.54            X63))
% 0.22/0.54          | ~ (v1_relat_1 @ X63))),
% 0.22/0.54      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.22/0.54  thf('54', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (((k3_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0) @ 
% 0.22/0.54            (k2_zfmisc_1 @ k1_xboole_0 @ 
% 0.22/0.54             (k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))))
% 0.22/0.54            = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.22/0.54          | ~ (v1_relat_1 @ X0)
% 0.22/0.54          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.22/0.54      inference('sup+', [status(thm)], ['52', '53'])).
% 0.22/0.54  thf('55', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.54      inference('sup+', [status(thm)], ['18', '21'])).
% 0.22/0.54  thf('56', plain,
% 0.22/0.54      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.54      inference('sup+', [status(thm)], ['14', '15'])).
% 0.22/0.54  thf('57', plain,
% 0.22/0.54      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.22/0.54         ((k2_zfmisc_1 @ (k4_xboole_0 @ X47 @ X49) @ X48)
% 0.22/0.54           = (k4_xboole_0 @ (k2_zfmisc_1 @ X47 @ X48) @ 
% 0.22/0.54              (k2_zfmisc_1 @ X49 @ X48)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.22/0.54  thf('58', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((k2_zfmisc_1 @ (k4_xboole_0 @ X1 @ X1) @ X0)
% 0.22/0.54           = (k5_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.22/0.54      inference('sup+', [status(thm)], ['56', '57'])).
% 0.22/0.54  thf('59', plain,
% 0.22/0.54      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.54      inference('sup+', [status(thm)], ['14', '15'])).
% 0.22/0.54  thf('60', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.54      inference('sup+', [status(thm)], ['18', '21'])).
% 0.22/0.54  thf('61', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((k2_zfmisc_1 @ (k5_xboole_0 @ X1 @ X1) @ X0) = (k1_xboole_0))),
% 0.22/0.54      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.22/0.54  thf('62', plain,
% 0.22/0.54      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.22/0.54      inference('sup+', [status(thm)], ['55', '61'])).
% 0.22/0.54  thf('63', plain,
% 0.22/0.54      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.54      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.54  thf('64', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.22/0.54          | ~ (v1_relat_1 @ X0)
% 0.22/0.54          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.22/0.54      inference('demod', [status(thm)], ['54', '62', '63'])).
% 0.22/0.54  thf('65', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (v1_relat_1 @ X0)
% 0.22/0.54          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.54          | ~ (v1_relat_1 @ X0)
% 0.22/0.54          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['44', '64'])).
% 0.22/0.54  thf('66', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.54      inference('clc', [status(thm)], ['11', '23'])).
% 0.22/0.54  thf('67', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (v1_relat_1 @ X0)
% 0.22/0.54          | ~ (v1_relat_1 @ X0)
% 0.22/0.54          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.22/0.54      inference('demod', [status(thm)], ['65', '66'])).
% 0.22/0.54  thf('68', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.22/0.54          | ~ (v1_relat_1 @ X0))),
% 0.22/0.54      inference('simplify', [status(thm)], ['67'])).
% 0.22/0.54  thf('69', plain,
% 0.22/0.54      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.22/0.54         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.54      inference('split', [status(esa)], ['42'])).
% 0.22/0.54  thf('70', plain,
% 0.22/0.54      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A)))
% 0.22/0.54         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['68', '69'])).
% 0.22/0.54  thf('71', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('72', plain,
% 0.22/0.54      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.22/0.54         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.54      inference('demod', [status(thm)], ['70', '71'])).
% 0.22/0.54  thf('73', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.22/0.54      inference('simplify', [status(thm)], ['72'])).
% 0.22/0.54  thf('74', plain,
% 0.22/0.54      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.22/0.54       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.22/0.54      inference('split', [status(esa)], ['42'])).
% 0.22/0.54  thf('75', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.22/0.54      inference('sat_resolution*', [status(thm)], ['73', '74'])).
% 0.22/0.54  thf('76', plain, (((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.54      inference('simpl_trail', [status(thm)], ['43', '75'])).
% 0.22/0.54  thf('77', plain,
% 0.22/0.54      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['41', '76'])).
% 0.22/0.54  thf('78', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('79', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.54      inference('demod', [status(thm)], ['77', '78'])).
% 0.22/0.54  thf('80', plain, ($false), inference('simplify', [status(thm)], ['79'])).
% 0.22/0.54  
% 0.22/0.54  % SZS output end Refutation
% 0.22/0.54  
% 0.22/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
