%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.48dpx33thT

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:28 EST 2020

% Result     : Theorem 1.05s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 432 expanded)
%              Number of leaves         :   33 ( 129 expanded)
%              Depth                    :   23
%              Number of atoms          :  915 (4778 expanded)
%              Number of equality atoms :  150 ( 904 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t43_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B = k1_xboole_0 )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B = k1_xboole_0 )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_zfmisc_1])).

thf('0',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( sk_C_2
     != ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('5',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( X10 != X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('8',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('10',plain,(
    ! [X64: $i,X65: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X64 ) @ X65 )
      | ( r2_hidden @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t67_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ B @ C ) )
     => ( A = k1_xboole_0 ) ) )).

thf('13',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( X16 = k1_xboole_0 )
      | ~ ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_tarski @ X16 @ X18 )
      | ~ ( r1_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t67_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf(t37_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('17',plain,(
    ! [X69: $i,X71: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X69 ) @ X71 )
      | ~ ( r2_hidden @ X69 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t37_zfmisc_1])).

thf('18',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ sk_B ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('22',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k2_xboole_0 @ sk_B @ sk_C_2 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,
    ( ( sk_B
     != ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','28'])).

thf('30',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['4','6','33'])).

thf('35',plain,(
    sk_C_2
 != ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['3','34'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('36',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('37',plain,(
    ! [X15: $i] :
      ( r1_xboole_0 @ X15 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('38',plain,(
    ! [X62: $i,X63: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X62 ) @ X63 )
      | ~ ( r2_hidden @ X62 @ X63 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('41',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_xboole_0 @ X14 @ X13 )
        = X13 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k2_xboole_0 @ sk_B @ sk_C_2 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('44',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k3_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X25 @ X26 ) @ ( k2_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('45',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('46',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k3_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ X25 @ ( k5_xboole_0 @ X26 @ ( k2_xboole_0 @ X25 @ X26 ) ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_C_2 @ sk_B ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('49',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_C_2 ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('50',plain,(
    ! [X24: $i] :
      ( ( k5_xboole_0 @ X24 @ X24 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('51',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('53',plain,(
    ! [X27: $i] :
      ( ( k2_tarski @ X27 @ X27 )
      = ( k1_tarski @ X27 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('54',plain,(
    ! [X68: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X68 ) )
      = X68 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('56',plain,(
    ! [X66: $i,X67: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X66 @ X67 ) )
      = ( k2_xboole_0 @ X66 @ X67 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k3_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ X25 @ ( k5_xboole_0 @ X26 @ ( k2_xboole_0 @ X25 @ X26 ) ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('60',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('61',plain,(
    ! [X24: $i] :
      ( ( k5_xboole_0 @ X24 @ X24 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','64'])).

thf('66',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
      = sk_C_2 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','65'])).

thf('67',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k2_xboole_0 @ sk_B @ sk_C_2 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('68',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k2_xboole_0 @ sk_B @ sk_C_2 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ( sk_B = k1_xboole_0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X69: $i,X71: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X69 ) @ X71 )
      | ~ ( r2_hidden @ X69 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t37_zfmisc_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( sk_B = k1_xboole_0 )
      | ( r1_xboole_0 @ sk_B @ X0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['67','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ( sk_B = k1_xboole_0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_xboole_0 @ X14 @ X13 )
        = X13 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( r1_xboole_0 @ sk_B @ X0 )
      | ( ( k2_xboole_0 @ sk_B @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('79',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k2_xboole_0 @ sk_B @ X0 )
        = X0 )
      | ( sk_B = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    sk_C_2
 != ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['3','34'])).

thf('82',plain,
    ( ( sk_C_2 != sk_C_2 )
    | ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['66','83'])).

thf('85',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,
    ( ( sk_C_2 != k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('87',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('89',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ sk_B @ X0 )
        = X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    sk_C_2
 != ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['3','34'])).

thf('91',plain,
    ( ( sk_C_2 != sk_C_2 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ( sk_C_2 != k1_xboole_0 )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['26'])).

thf('94',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['92','93'])).

thf('95',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['86','94'])).

thf('96',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['85','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['42','96'])).

thf('98',plain,(
    sk_C_2 != sk_C_2 ),
    inference(demod,[status(thm)],['35','97'])).

thf('99',plain,(
    $false ),
    inference(simplify,[status(thm)],['98'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.48dpx33thT
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:05:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.05/1.23  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.05/1.23  % Solved by: fo/fo7.sh
% 1.05/1.23  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.05/1.23  % done 1149 iterations in 0.778s
% 1.05/1.23  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.05/1.23  % SZS output start Refutation
% 1.05/1.23  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.05/1.23  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.05/1.23  thf(sk_A_type, type, sk_A: $i).
% 1.05/1.23  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.05/1.23  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.05/1.23  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.05/1.23  thf(sk_C_2_type, type, sk_C_2: $i).
% 1.05/1.23  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.05/1.23  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.05/1.23  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.05/1.23  thf(sk_B_type, type, sk_B: $i).
% 1.05/1.23  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.05/1.23  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.05/1.23  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.05/1.23  thf(t43_zfmisc_1, conjecture,
% 1.05/1.23    (![A:$i,B:$i,C:$i]:
% 1.05/1.23     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 1.05/1.23          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.05/1.23          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.05/1.23          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 1.05/1.23  thf(zf_stmt_0, negated_conjecture,
% 1.05/1.23    (~( ![A:$i,B:$i,C:$i]:
% 1.05/1.23        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 1.05/1.23             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.05/1.23             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.05/1.23             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 1.05/1.23    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 1.05/1.23  thf('0', plain,
% 1.05/1.23      ((((sk_B) != (k1_xboole_0)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf('1', plain,
% 1.05/1.23      ((((sk_C_2) != (k1_tarski @ sk_A)))
% 1.05/1.23         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 1.05/1.23      inference('split', [status(esa)], ['0'])).
% 1.05/1.23  thf('2', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf('3', plain,
% 1.05/1.23      ((((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2)))
% 1.05/1.23         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 1.05/1.23      inference('demod', [status(thm)], ['1', '2'])).
% 1.05/1.23  thf('4', plain,
% 1.05/1.23      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_xboole_0)))),
% 1.05/1.23      inference('split', [status(esa)], ['0'])).
% 1.05/1.23  thf('5', plain,
% 1.05/1.23      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf('6', plain,
% 1.05/1.23      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 1.05/1.23      inference('split', [status(esa)], ['5'])).
% 1.05/1.23  thf(d10_xboole_0, axiom,
% 1.05/1.23    (![A:$i,B:$i]:
% 1.05/1.23     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.05/1.23  thf('7', plain,
% 1.05/1.23      (![X10 : $i, X11 : $i]: ((r1_tarski @ X10 @ X11) | ((X10) != (X11)))),
% 1.05/1.23      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.05/1.23  thf('8', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 1.05/1.23      inference('simplify', [status(thm)], ['7'])).
% 1.05/1.23  thf('9', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf(l27_zfmisc_1, axiom,
% 1.05/1.23    (![A:$i,B:$i]:
% 1.05/1.23     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 1.05/1.23  thf('10', plain,
% 1.05/1.23      (![X64 : $i, X65 : $i]:
% 1.05/1.23         ((r1_xboole_0 @ (k1_tarski @ X64) @ X65) | (r2_hidden @ X64 @ X65))),
% 1.05/1.23      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 1.05/1.23  thf('11', plain,
% 1.05/1.23      (![X0 : $i]:
% 1.05/1.23         ((r1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ X0)
% 1.05/1.23          | (r2_hidden @ sk_A @ X0))),
% 1.05/1.23      inference('sup+', [status(thm)], ['9', '10'])).
% 1.05/1.23  thf(t7_xboole_1, axiom,
% 1.05/1.23    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.05/1.23  thf('12', plain,
% 1.05/1.23      (![X19 : $i, X20 : $i]: (r1_tarski @ X19 @ (k2_xboole_0 @ X19 @ X20))),
% 1.05/1.23      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.05/1.23  thf(t67_xboole_1, axiom,
% 1.05/1.23    (![A:$i,B:$i,C:$i]:
% 1.05/1.23     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 1.05/1.23         ( r1_xboole_0 @ B @ C ) ) =>
% 1.05/1.23       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.05/1.23  thf('13', plain,
% 1.05/1.23      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.05/1.23         (((X16) = (k1_xboole_0))
% 1.05/1.23          | ~ (r1_tarski @ X16 @ X17)
% 1.05/1.23          | ~ (r1_tarski @ X16 @ X18)
% 1.05/1.23          | ~ (r1_xboole_0 @ X17 @ X18))),
% 1.05/1.23      inference('cnf', [status(esa)], [t67_xboole_1])).
% 1.05/1.23  thf('14', plain,
% 1.05/1.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.23         (~ (r1_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 1.05/1.23          | ~ (r1_tarski @ X1 @ X2)
% 1.05/1.23          | ((X1) = (k1_xboole_0)))),
% 1.05/1.23      inference('sup-', [status(thm)], ['12', '13'])).
% 1.05/1.23  thf('15', plain,
% 1.05/1.23      (![X0 : $i]:
% 1.05/1.23         ((r2_hidden @ sk_A @ X0)
% 1.05/1.23          | ((sk_B) = (k1_xboole_0))
% 1.05/1.23          | ~ (r1_tarski @ sk_B @ X0))),
% 1.05/1.23      inference('sup-', [status(thm)], ['11', '14'])).
% 1.05/1.23  thf('16', plain, ((((sk_B) = (k1_xboole_0)) | (r2_hidden @ sk_A @ sk_B))),
% 1.05/1.23      inference('sup-', [status(thm)], ['8', '15'])).
% 1.05/1.23  thf(t37_zfmisc_1, axiom,
% 1.05/1.23    (![A:$i,B:$i]:
% 1.05/1.23     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 1.05/1.23  thf('17', plain,
% 1.05/1.23      (![X69 : $i, X71 : $i]:
% 1.05/1.23         ((r1_tarski @ (k1_tarski @ X69) @ X71) | ~ (r2_hidden @ X69 @ X71))),
% 1.05/1.23      inference('cnf', [status(esa)], [t37_zfmisc_1])).
% 1.05/1.23  thf('18', plain,
% 1.05/1.23      ((((sk_B) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ sk_A) @ sk_B))),
% 1.05/1.23      inference('sup-', [status(thm)], ['16', '17'])).
% 1.05/1.23  thf('19', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf('20', plain,
% 1.05/1.23      ((((sk_B) = (k1_xboole_0))
% 1.05/1.23        | (r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C_2) @ sk_B))),
% 1.05/1.23      inference('demod', [status(thm)], ['18', '19'])).
% 1.05/1.23  thf('21', plain,
% 1.05/1.23      (![X19 : $i, X20 : $i]: (r1_tarski @ X19 @ (k2_xboole_0 @ X19 @ X20))),
% 1.05/1.23      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.05/1.23  thf('22', plain,
% 1.05/1.23      (![X10 : $i, X12 : $i]:
% 1.05/1.23         (((X10) = (X12))
% 1.05/1.23          | ~ (r1_tarski @ X12 @ X10)
% 1.05/1.23          | ~ (r1_tarski @ X10 @ X12))),
% 1.05/1.23      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.05/1.23  thf('23', plain,
% 1.05/1.23      (![X0 : $i, X1 : $i]:
% 1.05/1.23         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 1.05/1.23          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 1.05/1.23      inference('sup-', [status(thm)], ['21', '22'])).
% 1.05/1.23  thf('24', plain,
% 1.05/1.23      ((((sk_B) = (k1_xboole_0)) | ((k2_xboole_0 @ sk_B @ sk_C_2) = (sk_B)))),
% 1.05/1.23      inference('sup-', [status(thm)], ['20', '23'])).
% 1.05/1.23  thf('25', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf('26', plain,
% 1.05/1.23      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_xboole_0)))),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf('27', plain,
% 1.05/1.23      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.05/1.23      inference('split', [status(esa)], ['26'])).
% 1.05/1.23  thf('28', plain,
% 1.05/1.23      ((((sk_B) != (k2_xboole_0 @ sk_B @ sk_C_2)))
% 1.05/1.23         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.05/1.23      inference('sup-', [status(thm)], ['25', '27'])).
% 1.05/1.23  thf('29', plain,
% 1.05/1.23      (((((sk_B) != (sk_B)) | ((sk_B) = (k1_xboole_0))))
% 1.05/1.23         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.05/1.23      inference('sup-', [status(thm)], ['24', '28'])).
% 1.05/1.23  thf('30', plain,
% 1.05/1.23      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.05/1.23      inference('simplify', [status(thm)], ['29'])).
% 1.05/1.23  thf('31', plain,
% 1.05/1.23      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 1.05/1.23      inference('split', [status(esa)], ['0'])).
% 1.05/1.23  thf('32', plain,
% 1.05/1.23      ((((sk_B) != (sk_B)))
% 1.05/1.23         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.05/1.23      inference('sup-', [status(thm)], ['30', '31'])).
% 1.05/1.23  thf('33', plain,
% 1.05/1.23      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 1.05/1.23      inference('simplify', [status(thm)], ['32'])).
% 1.05/1.23  thf('34', plain, (~ (((sk_C_2) = (k1_tarski @ sk_A)))),
% 1.05/1.23      inference('sat_resolution*', [status(thm)], ['4', '6', '33'])).
% 1.05/1.23  thf('35', plain, (((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2))),
% 1.05/1.23      inference('simpl_trail', [status(thm)], ['3', '34'])).
% 1.05/1.23  thf(d3_tarski, axiom,
% 1.05/1.23    (![A:$i,B:$i]:
% 1.05/1.23     ( ( r1_tarski @ A @ B ) <=>
% 1.05/1.23       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.05/1.23  thf('36', plain,
% 1.05/1.23      (![X3 : $i, X5 : $i]:
% 1.05/1.23         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 1.05/1.23      inference('cnf', [status(esa)], [d3_tarski])).
% 1.05/1.23  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 1.05/1.23  thf('37', plain, (![X15 : $i]: (r1_xboole_0 @ X15 @ k1_xboole_0)),
% 1.05/1.23      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.05/1.23  thf(l24_zfmisc_1, axiom,
% 1.05/1.23    (![A:$i,B:$i]:
% 1.05/1.23     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 1.05/1.23  thf('38', plain,
% 1.05/1.23      (![X62 : $i, X63 : $i]:
% 1.05/1.23         (~ (r1_xboole_0 @ (k1_tarski @ X62) @ X63) | ~ (r2_hidden @ X62 @ X63))),
% 1.05/1.23      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 1.05/1.23  thf('39', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.05/1.23      inference('sup-', [status(thm)], ['37', '38'])).
% 1.05/1.23  thf('40', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.05/1.23      inference('sup-', [status(thm)], ['36', '39'])).
% 1.05/1.23  thf(t12_xboole_1, axiom,
% 1.05/1.23    (![A:$i,B:$i]:
% 1.05/1.23     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.05/1.23  thf('41', plain,
% 1.05/1.23      (![X13 : $i, X14 : $i]:
% 1.05/1.23         (((k2_xboole_0 @ X14 @ X13) = (X13)) | ~ (r1_tarski @ X14 @ X13))),
% 1.05/1.23      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.05/1.23  thf('42', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.05/1.23      inference('sup-', [status(thm)], ['40', '41'])).
% 1.05/1.23  thf('43', plain,
% 1.05/1.23      ((((sk_B) = (k1_xboole_0)) | ((k2_xboole_0 @ sk_B @ sk_C_2) = (sk_B)))),
% 1.05/1.23      inference('sup-', [status(thm)], ['20', '23'])).
% 1.05/1.23  thf(t95_xboole_1, axiom,
% 1.05/1.23    (![A:$i,B:$i]:
% 1.05/1.23     ( ( k3_xboole_0 @ A @ B ) =
% 1.05/1.23       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 1.05/1.23  thf('44', plain,
% 1.05/1.23      (![X25 : $i, X26 : $i]:
% 1.05/1.23         ((k3_xboole_0 @ X25 @ X26)
% 1.05/1.23           = (k5_xboole_0 @ (k5_xboole_0 @ X25 @ X26) @ 
% 1.05/1.23              (k2_xboole_0 @ X25 @ X26)))),
% 1.05/1.23      inference('cnf', [status(esa)], [t95_xboole_1])).
% 1.05/1.23  thf(t91_xboole_1, axiom,
% 1.05/1.23    (![A:$i,B:$i,C:$i]:
% 1.05/1.23     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.05/1.23       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.05/1.23  thf('45', plain,
% 1.05/1.23      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.05/1.23         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 1.05/1.23           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 1.05/1.23      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.05/1.23  thf('46', plain,
% 1.05/1.23      (![X25 : $i, X26 : $i]:
% 1.05/1.23         ((k3_xboole_0 @ X25 @ X26)
% 1.05/1.23           = (k5_xboole_0 @ X25 @ 
% 1.05/1.23              (k5_xboole_0 @ X26 @ (k2_xboole_0 @ X25 @ X26))))),
% 1.05/1.23      inference('demod', [status(thm)], ['44', '45'])).
% 1.05/1.23  thf('47', plain,
% 1.05/1.23      ((((k3_xboole_0 @ sk_B @ sk_C_2)
% 1.05/1.23          = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_C_2 @ sk_B)))
% 1.05/1.23        | ((sk_B) = (k1_xboole_0)))),
% 1.05/1.23      inference('sup+', [status(thm)], ['43', '46'])).
% 1.05/1.23  thf(commutativity_k5_xboole_0, axiom,
% 1.05/1.23    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 1.05/1.23  thf('48', plain,
% 1.05/1.23      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.05/1.23      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.05/1.23  thf('49', plain,
% 1.05/1.23      ((((k3_xboole_0 @ sk_B @ sk_C_2)
% 1.05/1.23          = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ sk_C_2)))
% 1.05/1.23        | ((sk_B) = (k1_xboole_0)))),
% 1.05/1.23      inference('demod', [status(thm)], ['47', '48'])).
% 1.05/1.23  thf(t92_xboole_1, axiom,
% 1.05/1.23    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.05/1.23  thf('50', plain, (![X24 : $i]: ((k5_xboole_0 @ X24 @ X24) = (k1_xboole_0))),
% 1.05/1.23      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.05/1.23  thf('51', plain,
% 1.05/1.23      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.05/1.23         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 1.05/1.23           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 1.05/1.23      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.05/1.23  thf('52', plain,
% 1.05/1.23      (![X0 : $i, X1 : $i]:
% 1.05/1.23         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.05/1.23           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.05/1.23      inference('sup+', [status(thm)], ['50', '51'])).
% 1.05/1.23  thf(t69_enumset1, axiom,
% 1.05/1.23    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.05/1.23  thf('53', plain,
% 1.05/1.23      (![X27 : $i]: ((k2_tarski @ X27 @ X27) = (k1_tarski @ X27))),
% 1.05/1.23      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.05/1.23  thf(t31_zfmisc_1, axiom,
% 1.05/1.23    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 1.05/1.23  thf('54', plain, (![X68 : $i]: ((k3_tarski @ (k1_tarski @ X68)) = (X68))),
% 1.05/1.23      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 1.05/1.23  thf('55', plain, (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ X0)) = (X0))),
% 1.05/1.23      inference('sup+', [status(thm)], ['53', '54'])).
% 1.05/1.23  thf(l51_zfmisc_1, axiom,
% 1.05/1.23    (![A:$i,B:$i]:
% 1.05/1.23     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.05/1.23  thf('56', plain,
% 1.05/1.23      (![X66 : $i, X67 : $i]:
% 1.05/1.23         ((k3_tarski @ (k2_tarski @ X66 @ X67)) = (k2_xboole_0 @ X66 @ X67))),
% 1.05/1.23      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.05/1.23  thf('57', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 1.05/1.23      inference('demod', [status(thm)], ['55', '56'])).
% 1.05/1.23  thf('58', plain,
% 1.05/1.23      (![X25 : $i, X26 : $i]:
% 1.05/1.23         ((k3_xboole_0 @ X25 @ X26)
% 1.05/1.23           = (k5_xboole_0 @ X25 @ 
% 1.05/1.23              (k5_xboole_0 @ X26 @ (k2_xboole_0 @ X25 @ X26))))),
% 1.05/1.23      inference('demod', [status(thm)], ['44', '45'])).
% 1.05/1.23  thf('59', plain,
% 1.05/1.23      (![X0 : $i]:
% 1.05/1.23         ((k3_xboole_0 @ X0 @ X0)
% 1.05/1.23           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 1.05/1.23      inference('sup+', [status(thm)], ['57', '58'])).
% 1.05/1.23  thf(idempotence_k3_xboole_0, axiom,
% 1.05/1.23    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.05/1.23  thf('60', plain, (![X9 : $i]: ((k3_xboole_0 @ X9 @ X9) = (X9))),
% 1.05/1.23      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.05/1.23  thf('61', plain, (![X24 : $i]: ((k5_xboole_0 @ X24 @ X24) = (k1_xboole_0))),
% 1.05/1.23      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.05/1.23  thf('62', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.05/1.23      inference('demod', [status(thm)], ['59', '60', '61'])).
% 1.05/1.23  thf('63', plain,
% 1.05/1.23      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.05/1.23      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.05/1.23  thf('64', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.05/1.23      inference('sup+', [status(thm)], ['62', '63'])).
% 1.05/1.23  thf('65', plain,
% 1.05/1.23      (![X0 : $i, X1 : $i]:
% 1.05/1.23         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.05/1.23      inference('demod', [status(thm)], ['52', '64'])).
% 1.05/1.23  thf('66', plain,
% 1.05/1.23      ((((k3_xboole_0 @ sk_B @ sk_C_2) = (sk_C_2)) | ((sk_B) = (k1_xboole_0)))),
% 1.05/1.23      inference('demod', [status(thm)], ['49', '65'])).
% 1.05/1.23  thf('67', plain,
% 1.05/1.23      ((((sk_B) = (k1_xboole_0)) | ((k2_xboole_0 @ sk_B @ sk_C_2) = (sk_B)))),
% 1.05/1.23      inference('sup-', [status(thm)], ['20', '23'])).
% 1.05/1.23  thf('68', plain,
% 1.05/1.23      ((((sk_B) = (k1_xboole_0)) | ((k2_xboole_0 @ sk_B @ sk_C_2) = (sk_B)))),
% 1.05/1.23      inference('sup-', [status(thm)], ['20', '23'])).
% 1.05/1.23  thf('69', plain,
% 1.05/1.23      (![X0 : $i]:
% 1.05/1.23         ((r1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ X0)
% 1.05/1.23          | (r2_hidden @ sk_A @ X0))),
% 1.05/1.23      inference('sup+', [status(thm)], ['9', '10'])).
% 1.05/1.23  thf('70', plain,
% 1.05/1.23      (![X0 : $i]:
% 1.05/1.23         ((r1_xboole_0 @ sk_B @ X0)
% 1.05/1.23          | ((sk_B) = (k1_xboole_0))
% 1.05/1.23          | (r2_hidden @ sk_A @ X0))),
% 1.05/1.23      inference('sup+', [status(thm)], ['68', '69'])).
% 1.05/1.23  thf('71', plain,
% 1.05/1.23      (![X69 : $i, X71 : $i]:
% 1.05/1.23         ((r1_tarski @ (k1_tarski @ X69) @ X71) | ~ (r2_hidden @ X69 @ X71))),
% 1.05/1.23      inference('cnf', [status(esa)], [t37_zfmisc_1])).
% 1.05/1.23  thf('72', plain,
% 1.05/1.23      (![X0 : $i]:
% 1.05/1.23         (((sk_B) = (k1_xboole_0))
% 1.05/1.23          | (r1_xboole_0 @ sk_B @ X0)
% 1.05/1.23          | (r1_tarski @ (k1_tarski @ sk_A) @ X0))),
% 1.05/1.23      inference('sup-', [status(thm)], ['70', '71'])).
% 1.05/1.23  thf('73', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 1.05/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.23  thf('74', plain,
% 1.05/1.23      (![X0 : $i]:
% 1.05/1.23         (((sk_B) = (k1_xboole_0))
% 1.05/1.23          | (r1_xboole_0 @ sk_B @ X0)
% 1.05/1.23          | (r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C_2) @ X0))),
% 1.05/1.23      inference('demod', [status(thm)], ['72', '73'])).
% 1.05/1.23  thf('75', plain,
% 1.05/1.23      (![X0 : $i]:
% 1.05/1.23         ((r1_tarski @ sk_B @ X0)
% 1.05/1.23          | ((sk_B) = (k1_xboole_0))
% 1.05/1.23          | (r1_xboole_0 @ sk_B @ X0)
% 1.05/1.23          | ((sk_B) = (k1_xboole_0)))),
% 1.05/1.23      inference('sup+', [status(thm)], ['67', '74'])).
% 1.05/1.23  thf('76', plain,
% 1.05/1.23      (![X0 : $i]:
% 1.05/1.23         ((r1_xboole_0 @ sk_B @ X0)
% 1.05/1.23          | ((sk_B) = (k1_xboole_0))
% 1.05/1.23          | (r1_tarski @ sk_B @ X0))),
% 1.05/1.23      inference('simplify', [status(thm)], ['75'])).
% 1.05/1.23  thf('77', plain,
% 1.05/1.23      (![X13 : $i, X14 : $i]:
% 1.05/1.23         (((k2_xboole_0 @ X14 @ X13) = (X13)) | ~ (r1_tarski @ X14 @ X13))),
% 1.05/1.23      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.05/1.23  thf('78', plain,
% 1.05/1.23      (![X0 : $i]:
% 1.05/1.23         (((sk_B) = (k1_xboole_0))
% 1.05/1.23          | (r1_xboole_0 @ sk_B @ X0)
% 1.05/1.23          | ((k2_xboole_0 @ sk_B @ X0) = (X0)))),
% 1.05/1.23      inference('sup-', [status(thm)], ['76', '77'])).
% 1.05/1.23  thf(d7_xboole_0, axiom,
% 1.05/1.23    (![A:$i,B:$i]:
% 1.05/1.23     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.05/1.23       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.05/1.23  thf('79', plain,
% 1.05/1.23      (![X6 : $i, X7 : $i]:
% 1.05/1.23         (((k3_xboole_0 @ X6 @ X7) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 1.05/1.23      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.05/1.23  thf('80', plain,
% 1.05/1.23      (![X0 : $i]:
% 1.05/1.23         (((k2_xboole_0 @ sk_B @ X0) = (X0))
% 1.05/1.23          | ((sk_B) = (k1_xboole_0))
% 1.05/1.23          | ((k3_xboole_0 @ sk_B @ X0) = (k1_xboole_0)))),
% 1.05/1.23      inference('sup-', [status(thm)], ['78', '79'])).
% 1.05/1.23  thf('81', plain, (((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2))),
% 1.05/1.23      inference('simpl_trail', [status(thm)], ['3', '34'])).
% 1.05/1.23  thf('82', plain,
% 1.05/1.23      ((((sk_C_2) != (sk_C_2))
% 1.05/1.23        | ((k3_xboole_0 @ sk_B @ sk_C_2) = (k1_xboole_0))
% 1.05/1.23        | ((sk_B) = (k1_xboole_0)))),
% 1.05/1.23      inference('sup-', [status(thm)], ['80', '81'])).
% 1.05/1.23  thf('83', plain,
% 1.05/1.23      ((((sk_B) = (k1_xboole_0))
% 1.05/1.23        | ((k3_xboole_0 @ sk_B @ sk_C_2) = (k1_xboole_0)))),
% 1.05/1.23      inference('simplify', [status(thm)], ['82'])).
% 1.05/1.23  thf('84', plain,
% 1.05/1.23      ((((sk_C_2) = (k1_xboole_0))
% 1.05/1.23        | ((sk_B) = (k1_xboole_0))
% 1.05/1.23        | ((sk_B) = (k1_xboole_0)))),
% 1.05/1.23      inference('sup+', [status(thm)], ['66', '83'])).
% 1.05/1.23  thf('85', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_C_2) = (k1_xboole_0)))),
% 1.05/1.23      inference('simplify', [status(thm)], ['84'])).
% 1.05/1.23  thf('86', plain,
% 1.05/1.23      ((((sk_C_2) != (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 1.05/1.23      inference('split', [status(esa)], ['26'])).
% 1.05/1.23  thf('87', plain,
% 1.05/1.23      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.05/1.23      inference('simplify', [status(thm)], ['29'])).
% 1.05/1.23  thf('88', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.05/1.23      inference('sup-', [status(thm)], ['40', '41'])).
% 1.05/1.23  thf('89', plain,
% 1.05/1.23      ((![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0)))
% 1.05/1.23         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.05/1.23      inference('sup+', [status(thm)], ['87', '88'])).
% 1.05/1.23  thf('90', plain, (((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2))),
% 1.05/1.23      inference('simpl_trail', [status(thm)], ['3', '34'])).
% 1.05/1.23  thf('91', plain,
% 1.05/1.23      ((((sk_C_2) != (sk_C_2))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.05/1.23      inference('sup-', [status(thm)], ['89', '90'])).
% 1.05/1.23  thf('92', plain, ((((sk_B) = (k1_tarski @ sk_A)))),
% 1.05/1.23      inference('simplify', [status(thm)], ['91'])).
% 1.05/1.23  thf('93', plain,
% 1.05/1.23      (~ (((sk_C_2) = (k1_xboole_0))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 1.05/1.23      inference('split', [status(esa)], ['26'])).
% 1.05/1.23  thf('94', plain, (~ (((sk_C_2) = (k1_xboole_0)))),
% 1.05/1.23      inference('sat_resolution*', [status(thm)], ['92', '93'])).
% 1.05/1.23  thf('95', plain, (((sk_C_2) != (k1_xboole_0))),
% 1.05/1.23      inference('simpl_trail', [status(thm)], ['86', '94'])).
% 1.05/1.23  thf('96', plain, (((sk_B) = (k1_xboole_0))),
% 1.05/1.23      inference('simplify_reflect-', [status(thm)], ['85', '95'])).
% 1.05/1.23  thf('97', plain, (![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0))),
% 1.05/1.23      inference('demod', [status(thm)], ['42', '96'])).
% 1.05/1.23  thf('98', plain, (((sk_C_2) != (sk_C_2))),
% 1.05/1.23      inference('demod', [status(thm)], ['35', '97'])).
% 1.05/1.23  thf('99', plain, ($false), inference('simplify', [status(thm)], ['98'])).
% 1.05/1.23  
% 1.05/1.23  % SZS output end Refutation
% 1.05/1.23  
% 1.05/1.24  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
