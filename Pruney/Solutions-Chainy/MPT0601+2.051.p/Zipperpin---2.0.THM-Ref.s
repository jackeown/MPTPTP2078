%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WS3111dpFG

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:48 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 378 expanded)
%              Number of leaves         :   29 ( 114 expanded)
%              Depth                    :   19
%              Number of atoms          :  677 (3603 expanded)
%              Number of equality atoms :   68 ( 280 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('1',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( r2_hidden @ X43 @ ( k11_relat_1 @ X44 @ X45 ) )
      | ( r2_hidden @ ( k4_tarski @ X45 @ X43 ) @ X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_B @ ( k11_relat_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('3',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X36 @ X37 ) @ X38 )
      | ( r2_hidden @ X36 @ X39 )
      | ( X39
       != ( k1_relat_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('4',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( r2_hidden @ X36 @ ( k1_relat_1 @ X38 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X36 @ X37 ) @ X38 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf(t205_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
        <=> ( ( k11_relat_1 @ B @ A )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t205_relat_1])).

thf('6',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('11',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('12',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ X40 @ X39 )
      | ( r2_hidden @ ( k4_tarski @ X40 @ ( sk_D_1 @ X40 @ X38 ) ) @ X38 )
      | ( X39
       != ( k1_relat_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('13',plain,(
    ! [X38: $i,X40: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X40 @ ( sk_D_1 @ X40 @ X38 ) ) @ X38 )
      | ~ ( r2_hidden @ X40 @ ( k1_relat_1 @ X38 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_1 @ sk_A @ sk_B_1 ) ) @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X45 @ X43 ) @ X44 )
      | ( r2_hidden @ X43 @ ( k11_relat_1 @ X44 @ X45 ) )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('16',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_1 )
      | ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B_1 ) @ ( k11_relat_1 @ sk_B_1 @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B_1 ) @ ( k11_relat_1 @ sk_B_1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('19',plain,(
    ! [X26: $i,X28: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X26 ) @ X28 )
      | ~ ( r2_hidden @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('20',plain,
    ( ( r1_tarski @ ( k1_tarski @ ( sk_D_1 @ sk_A @ sk_B_1 ) ) @ ( k11_relat_1 @ sk_B_1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r1_tarski @ ( k1_tarski @ ( sk_D_1 @ sk_A @ sk_B_1 ) ) @ k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['10','20'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('22',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('23',plain,
    ( ( ( k1_tarski @ ( sk_D_1 @ sk_A @ sk_B_1 ) )
      = k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('24',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t19_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k1_tarski @ A ) ) )).

thf('25',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X29 ) @ ( k2_tarski @ X29 @ X30 ) )
      = ( k1_tarski @ X29 ) ) ),
    inference(cnf,[status(esa)],[t19_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('28',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X34 @ X35 ) )
      = ( k3_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ ( k1_tarski @ X0 ) ) )
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('31',plain,
    ( ( ( k1_setfam_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k1_tarski @ ( sk_D_1 @ sk_A @ sk_B_1 ) ) )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','30'])).

thf('32',plain,
    ( ( ( k1_tarski @ ( sk_D_1 @ sk_A @ sk_B_1 ) )
      = k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('33',plain,
    ( ( ( k1_setfam_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('35',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('38',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ X4 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('39',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k1_tarski @ ( sk_D_1 @ sk_A @ sk_B_1 ) )
      = k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('41',plain,(
    ! [X31: $i,X32: $i] :
      ( ( X32 != X31 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X32 ) @ ( k1_tarski @ X31 ) )
       != ( k1_tarski @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('42',plain,(
    ! [X31: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X31 ) @ ( k1_tarski @ X31 ) )
     != ( k1_tarski @ X31 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ ( sk_D_1 @ sk_A @ sk_B_1 ) ) @ k1_xboole_0 )
     != ( k1_tarski @ ( sk_D_1 @ sk_A @ sk_B_1 ) ) )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,
    ( ( ( k1_tarski @ ( sk_D_1 @ sk_A @ sk_B_1 ) )
      = k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('45',plain,
    ( ( ( k1_tarski @ ( sk_D_1 @ sk_A @ sk_B_1 ) )
      = k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('46',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['39','46'])).

thf('48',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['6'])).

thf('49',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['9','47','48'])).

thf('50',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(simpl_trail,[status(thm)],['7','49'])).

thf('51',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['5','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( k11_relat_1 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('55',plain,(
    ( k11_relat_1 @ sk_B_1 @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['9','47'])).

thf('56',plain,(
    ( k11_relat_1 @ sk_B_1 @ sk_A )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['54','55'])).

thf('57',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['53','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WS3111dpFG
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:58:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 173 iterations in 0.039s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.20/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.49  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.49  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.20/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.49  thf(t7_xboole_0, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.49          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.49  thf(t204_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ C ) =>
% 0.20/0.49       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.20/0.49         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X43 @ (k11_relat_1 @ X44 @ X45))
% 0.20/0.49          | (r2_hidden @ (k4_tarski @ X45 @ X43) @ X44)
% 0.20/0.49          | ~ (v1_relat_1 @ X44))),
% 0.20/0.49      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((k11_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.20/0.49          | ~ (v1_relat_1 @ X1)
% 0.20/0.49          | (r2_hidden @ (k4_tarski @ X0 @ (sk_B @ (k11_relat_1 @ X1 @ X0))) @ 
% 0.20/0.49             X1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.49  thf(d4_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.20/0.49       ( ![C:$i]:
% 0.20/0.49         ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.49           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.20/0.49         (~ (r2_hidden @ (k4_tarski @ X36 @ X37) @ X38)
% 0.20/0.49          | (r2_hidden @ X36 @ X39)
% 0.20/0.49          | ((X39) != (k1_relat_1 @ X38)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.20/0.49         ((r2_hidden @ X36 @ (k1_relat_1 @ X38))
% 0.20/0.49          | ~ (r2_hidden @ (k4_tarski @ X36 @ X37) @ X38))),
% 0.20/0.49      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X0)
% 0.20/0.49          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.20/0.49          | (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '4'])).
% 0.20/0.49  thf(t205_relat_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ B ) =>
% 0.20/0.49       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.20/0.49         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i]:
% 0.20/0.49        ( ( v1_relat_1 @ B ) =>
% 0.20/0.49          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.20/0.49            ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t205_relat_1])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.20/0.49        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 0.20/0.49         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.20/0.49      inference('split', [status(esa)], ['6'])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      ((((k11_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0))
% 0.20/0.49        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.20/0.49       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.20/0.49      inference('split', [status(esa)], ['8'])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.20/0.49         <= ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.49      inference('split', [status(esa)], ['6'])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 0.20/0.49         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.20/0.49      inference('split', [status(esa)], ['8'])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X40 @ X39)
% 0.20/0.49          | (r2_hidden @ (k4_tarski @ X40 @ (sk_D_1 @ X40 @ X38)) @ X38)
% 0.20/0.49          | ((X39) != (k1_relat_1 @ X38)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X38 : $i, X40 : $i]:
% 0.20/0.49         ((r2_hidden @ (k4_tarski @ X40 @ (sk_D_1 @ X40 @ X38)) @ X38)
% 0.20/0.49          | ~ (r2_hidden @ X40 @ (k1_relat_1 @ X38)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (((r2_hidden @ (k4_tarski @ sk_A @ (sk_D_1 @ sk_A @ sk_B_1)) @ sk_B_1))
% 0.20/0.49         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['11', '13'])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.20/0.49         (~ (r2_hidden @ (k4_tarski @ X45 @ X43) @ X44)
% 0.20/0.49          | (r2_hidden @ X43 @ (k11_relat_1 @ X44 @ X45))
% 0.20/0.49          | ~ (v1_relat_1 @ X44))),
% 0.20/0.49      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (((~ (v1_relat_1 @ sk_B_1)
% 0.20/0.49         | (r2_hidden @ (sk_D_1 @ sk_A @ sk_B_1) @ 
% 0.20/0.49            (k11_relat_1 @ sk_B_1 @ sk_A))))
% 0.20/0.49         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.49  thf('17', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_B_1) @ (k11_relat_1 @ sk_B_1 @ sk_A)))
% 0.20/0.49         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.20/0.49      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.49  thf(l1_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X26 : $i, X28 : $i]:
% 0.20/0.49         ((r1_tarski @ (k1_tarski @ X26) @ X28) | ~ (r2_hidden @ X26 @ X28))),
% 0.20/0.49      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (((r1_tarski @ (k1_tarski @ (sk_D_1 @ sk_A @ sk_B_1)) @ 
% 0.20/0.49         (k11_relat_1 @ sk_B_1 @ sk_A)))
% 0.20/0.49         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (((r1_tarski @ (k1_tarski @ (sk_D_1 @ sk_A @ sk_B_1)) @ k1_xboole_0))
% 0.20/0.49         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.20/0.49             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.49      inference('sup+', [status(thm)], ['10', '20'])).
% 0.20/0.49  thf(t3_xboole_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      ((((k1_tarski @ (sk_D_1 @ sk_A @ sk_B_1)) = (k1_xboole_0)))
% 0.20/0.49         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.20/0.49             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.49  thf(t69_enumset1, axiom,
% 0.20/0.49    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.49  thf('24', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.49  thf(t19_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.20/0.49       ( k1_tarski @ A ) ))).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X29 : $i, X30 : $i]:
% 0.20/0.49         ((k3_xboole_0 @ (k1_tarski @ X29) @ (k2_tarski @ X29 @ X30))
% 0.20/0.49           = (k1_tarski @ X29))),
% 0.20/0.49      inference('cnf', [status(esa)], [t19_zfmisc_1])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.20/0.49           = (k1_tarski @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['24', '25'])).
% 0.20/0.49  thf('27', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.49  thf(t12_setfam_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (![X34 : $i, X35 : $i]:
% 0.20/0.49         ((k1_setfam_1 @ (k2_tarski @ X34 @ X35)) = (k3_xboole_0 @ X34 @ X35))),
% 0.20/0.49      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['27', '28'])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((k1_setfam_1 @ (k1_tarski @ (k1_tarski @ X0))) = (k1_tarski @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['26', '29'])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      ((((k1_setfam_1 @ (k1_tarski @ k1_xboole_0))
% 0.20/0.49          = (k1_tarski @ (sk_D_1 @ sk_A @ sk_B_1))))
% 0.20/0.49         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.20/0.49             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.49      inference('sup+', [status(thm)], ['23', '30'])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      ((((k1_tarski @ (sk_D_1 @ sk_A @ sk_B_1)) = (k1_xboole_0)))
% 0.20/0.49         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.20/0.49             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      ((((k1_setfam_1 @ (k1_tarski @ k1_xboole_0)) = (k1_xboole_0)))
% 0.20/0.49         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.20/0.49             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.49      inference('sup+', [status(thm)], ['31', '32'])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['27', '28'])).
% 0.20/0.49  thf(t100_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      (![X1 : $i, X2 : $i]:
% 0.20/0.49         ((k4_xboole_0 @ X1 @ X2)
% 0.20/0.49           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((k4_xboole_0 @ X0 @ X0)
% 0.20/0.49           = (k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.20/0.49      inference('sup+', [status(thm)], ['34', '35'])).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      ((((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.20/0.49          = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0)))
% 0.20/0.49         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.20/0.49             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.49      inference('sup+', [status(thm)], ['33', '36'])).
% 0.20/0.49  thf(t92_xboole_1, axiom,
% 0.20/0.49    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.49  thf('38', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ X4) = (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      ((((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0)))
% 0.20/0.49         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.20/0.49             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.49      inference('demod', [status(thm)], ['37', '38'])).
% 0.20/0.49  thf('40', plain,
% 0.20/0.49      ((((k1_tarski @ (sk_D_1 @ sk_A @ sk_B_1)) = (k1_xboole_0)))
% 0.20/0.49         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.20/0.49             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.49  thf(t20_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.49         ( k1_tarski @ A ) ) <=>
% 0.20/0.49       ( ( A ) != ( B ) ) ))).
% 0.20/0.49  thf('41', plain,
% 0.20/0.49      (![X31 : $i, X32 : $i]:
% 0.20/0.49         (((X32) != (X31))
% 0.20/0.49          | ((k4_xboole_0 @ (k1_tarski @ X32) @ (k1_tarski @ X31))
% 0.20/0.49              != (k1_tarski @ X32)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      (![X31 : $i]:
% 0.20/0.49         ((k4_xboole_0 @ (k1_tarski @ X31) @ (k1_tarski @ X31))
% 0.20/0.49           != (k1_tarski @ X31))),
% 0.20/0.49      inference('simplify', [status(thm)], ['41'])).
% 0.20/0.49  thf('43', plain,
% 0.20/0.49      ((((k4_xboole_0 @ (k1_tarski @ (sk_D_1 @ sk_A @ sk_B_1)) @ k1_xboole_0)
% 0.20/0.49          != (k1_tarski @ (sk_D_1 @ sk_A @ sk_B_1))))
% 0.20/0.49         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.20/0.49             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['40', '42'])).
% 0.20/0.49  thf('44', plain,
% 0.20/0.49      ((((k1_tarski @ (sk_D_1 @ sk_A @ sk_B_1)) = (k1_xboole_0)))
% 0.20/0.49         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.20/0.49             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.49  thf('45', plain,
% 0.20/0.49      ((((k1_tarski @ (sk_D_1 @ sk_A @ sk_B_1)) = (k1_xboole_0)))
% 0.20/0.49         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.20/0.49             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.49  thf('46', plain,
% 0.20/0.49      ((((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.49         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.20/0.49             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.49      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.20/0.49  thf('47', plain,
% 0.20/0.49      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) | 
% 0.20/0.49       ~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['39', '46'])).
% 0.20/0.49  thf('48', plain,
% 0.20/0.49      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) | 
% 0.20/0.49       (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.20/0.49      inference('split', [status(esa)], ['6'])).
% 0.20/0.49  thf('49', plain, (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['9', '47', '48'])).
% 0.20/0.49  thf('50', plain, (~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['7', '49'])).
% 0.20/0.49  thf('51', plain,
% 0.20/0.49      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.20/0.49        | ~ (v1_relat_1 @ sk_B_1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['5', '50'])).
% 0.20/0.49  thf('52', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('53', plain, (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['51', '52'])).
% 0.20/0.49  thf('54', plain,
% 0.20/0.49      ((((k11_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0)))
% 0.20/0.49         <= (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.49      inference('split', [status(esa)], ['8'])).
% 0.20/0.49  thf('55', plain, (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['9', '47'])).
% 0.20/0.49  thf('56', plain, (((k11_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['54', '55'])).
% 0.20/0.49  thf('57', plain, ($false),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['53', '56'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
