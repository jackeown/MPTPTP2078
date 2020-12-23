%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hFuafepIjr

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:42 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 360 expanded)
%              Number of leaves         :   18 ( 117 expanded)
%              Depth                    :   25
%              Number of atoms          :  887 (3331 expanded)
%              Number of equality atoms :   82 ( 239 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
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

thf('9',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('10',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('21',plain,
    ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('23',plain,
    ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('24',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X24 @ X26 ) @ ( k3_xboole_0 @ X25 @ X27 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X24 @ X25 ) @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('25',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ ( k3_xboole_0 @ sk_D_1 @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X24 @ X26 ) @ ( k3_xboole_0 @ X25 @ X27 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X24 @ X25 ) @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) ) @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_D_1 @ sk_B ) ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X24 @ X26 ) @ ( k3_xboole_0 @ X25 @ X27 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X24 @ X25 ) @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) ) @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_D_1 @ sk_B ) ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_D_1 @ sk_B ) ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['18','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_D_1 @ sk_B ) ) )
      = ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ ( k3_xboole_0 @ sk_D_1 @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_D_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['7','32'])).

thf('34',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ ( k3_xboole_0 @ sk_D_1 @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('46',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34','35','44','45'])).

thf(t117_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) )
          | ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) )
        & ~ ( r1_tarski @ B @ C ) ) )).

thf('47',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( X17 = k1_xboole_0 )
      | ( r1_tarski @ X18 @ X19 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X17 @ X18 ) @ ( k2_zfmisc_1 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ X0 @ ( k3_xboole_0 @ sk_D_1 @ sk_B ) )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ ( k3_xboole_0 @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','48'])).

thf('50',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('51',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_D_1 @ sk_B ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','43'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('54',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_D_1 @ sk_B )
      = sk_B ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('56',plain,
    ( ( r1_tarski @ sk_B @ sk_D_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_1 )
    | ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D_1 )
   <= ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['57'])).

thf('59',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34','35','44','45'])).

thf('60',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ ( k3_xboole_0 @ sk_D_1 @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('61',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( X17 = k1_xboole_0 )
      | ( r1_tarski @ X18 @ X19 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X18 @ X17 ) @ ( k2_zfmisc_1 @ X19 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ ( k3_xboole_0 @ sk_D_1 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ X0 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) )
      | ( ( k3_xboole_0 @ sk_D_1 @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k3_xboole_0 @ sk_D_1 @ sk_B )
      = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('65',plain,
    ( ( ( k3_xboole_0 @ sk_D_1 @ sk_B )
      = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('67',plain,
    ( ( ( k3_xboole_0 @ sk_D_1 @ sk_B )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','43'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('70',plain,
    ( ( ( k3_xboole_0 @ sk_D_1 @ sk_B )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
      = sk_A ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ ( k3_xboole_0 @ sk_D_1 @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('72',plain,
    ( ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ k1_xboole_0 )
      = ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
      = sk_A ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('73',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_zfmisc_1 @ X15 @ X16 )
        = k1_xboole_0 )
      | ( X16 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('74',plain,(
    ! [X15: $i] :
      ( ( k2_zfmisc_1 @ X15 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ( k1_xboole_0
      = ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
      = sk_A ) ),
    inference(demod,[status(thm)],['72','74'])).

thf('76',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('79',plain,(
    r1_tarski @ sk_A @ sk_C_1 ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['57'])).

thf('81',plain,(
    r1_tarski @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D_1 )
    | ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['57'])).

thf('83',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference('sat_resolution*',[status(thm)],['81','82'])).

thf('84',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference(simpl_trail,[status(thm)],['58','83'])).

thf('85',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['56','84'])).

thf('86',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_zfmisc_1 @ X15 @ X16 )
        = k1_xboole_0 )
      | ( X15 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('87',plain,(
    ! [X16: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X16 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','85','87'])).

thf('89',plain,(
    $false ),
    inference(simplify,[status(thm)],['88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hFuafepIjr
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:12:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.55/0.75  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.55/0.75  % Solved by: fo/fo7.sh
% 0.55/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.75  % done 458 iterations in 0.299s
% 0.55/0.75  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.55/0.75  % SZS output start Refutation
% 0.55/0.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.55/0.75  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.55/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.55/0.75  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.55/0.75  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.55/0.75  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.75  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.55/0.75  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.55/0.75  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.55/0.75  thf(t138_zfmisc_1, conjecture,
% 0.55/0.75    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.75     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.55/0.75       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.55/0.75         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 0.55/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.75    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.75        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.55/0.75          ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.55/0.75            ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ) )),
% 0.55/0.75    inference('cnf.neg', [status(esa)], [t138_zfmisc_1])).
% 0.55/0.75  thf('0', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf(d3_tarski, axiom,
% 0.55/0.75    (![A:$i,B:$i]:
% 0.55/0.75     ( ( r1_tarski @ A @ B ) <=>
% 0.55/0.75       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.55/0.75  thf('1', plain,
% 0.55/0.75      (![X3 : $i, X5 : $i]:
% 0.55/0.75         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.55/0.75      inference('cnf', [status(esa)], [d3_tarski])).
% 0.55/0.75  thf('2', plain,
% 0.55/0.75      (![X3 : $i, X5 : $i]:
% 0.55/0.75         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.55/0.75      inference('cnf', [status(esa)], [d3_tarski])).
% 0.55/0.75  thf('3', plain,
% 0.55/0.75      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.55/0.75      inference('sup-', [status(thm)], ['1', '2'])).
% 0.55/0.75  thf('4', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.55/0.75      inference('simplify', [status(thm)], ['3'])).
% 0.55/0.75  thf('5', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.55/0.75      inference('simplify', [status(thm)], ['3'])).
% 0.55/0.75  thf(t28_xboole_1, axiom,
% 0.55/0.75    (![A:$i,B:$i]:
% 0.55/0.75     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.55/0.75  thf('6', plain,
% 0.55/0.75      (![X12 : $i, X13 : $i]:
% 0.55/0.75         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.55/0.75      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.55/0.75  thf('7', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.55/0.75      inference('sup-', [status(thm)], ['5', '6'])).
% 0.55/0.75  thf('8', plain,
% 0.55/0.75      (![X3 : $i, X5 : $i]:
% 0.55/0.75         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.55/0.75      inference('cnf', [status(esa)], [d3_tarski])).
% 0.55/0.75  thf(d4_xboole_0, axiom,
% 0.55/0.75    (![A:$i,B:$i,C:$i]:
% 0.55/0.75     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.55/0.75       ( ![D:$i]:
% 0.55/0.75         ( ( r2_hidden @ D @ C ) <=>
% 0.55/0.75           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.55/0.75  thf('9', plain,
% 0.55/0.75      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.55/0.75         (~ (r2_hidden @ X10 @ X9)
% 0.55/0.75          | (r2_hidden @ X10 @ X8)
% 0.55/0.75          | ((X9) != (k3_xboole_0 @ X7 @ X8)))),
% 0.55/0.75      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.55/0.75  thf('10', plain,
% 0.55/0.75      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.55/0.75         ((r2_hidden @ X10 @ X8)
% 0.55/0.75          | ~ (r2_hidden @ X10 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.55/0.75      inference('simplify', [status(thm)], ['9'])).
% 0.55/0.75  thf('11', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.75         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.55/0.75          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.55/0.75      inference('sup-', [status(thm)], ['8', '10'])).
% 0.55/0.75  thf('12', plain,
% 0.55/0.75      (![X3 : $i, X5 : $i]:
% 0.55/0.75         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.55/0.75      inference('cnf', [status(esa)], [d3_tarski])).
% 0.55/0.75  thf('13', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]:
% 0.55/0.75         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.55/0.75          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.55/0.75      inference('sup-', [status(thm)], ['11', '12'])).
% 0.55/0.75  thf('14', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.55/0.75      inference('simplify', [status(thm)], ['13'])).
% 0.55/0.75  thf('15', plain,
% 0.55/0.75      (![X12 : $i, X13 : $i]:
% 0.55/0.75         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.55/0.75      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.55/0.75  thf('16', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]:
% 0.55/0.75         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.55/0.75           = (k3_xboole_0 @ X1 @ X0))),
% 0.55/0.75      inference('sup-', [status(thm)], ['14', '15'])).
% 0.55/0.75  thf(commutativity_k3_xboole_0, axiom,
% 0.55/0.75    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.55/0.75  thf('17', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.55/0.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.55/0.75  thf('18', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]:
% 0.55/0.75         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.55/0.75           = (k3_xboole_0 @ X1 @ X0))),
% 0.55/0.75      inference('demod', [status(thm)], ['16', '17'])).
% 0.55/0.75  thf('19', plain,
% 0.55/0.75      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.55/0.75        (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('20', plain,
% 0.55/0.75      (![X12 : $i, X13 : $i]:
% 0.55/0.75         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.55/0.75      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.55/0.75  thf('21', plain,
% 0.55/0.75      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.55/0.75         (k2_zfmisc_1 @ sk_C_1 @ sk_D_1)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.55/0.75      inference('sup-', [status(thm)], ['19', '20'])).
% 0.55/0.75  thf('22', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.55/0.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.55/0.75  thf('23', plain,
% 0.55/0.75      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 0.55/0.75         (k2_zfmisc_1 @ sk_A @ sk_B)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.55/0.75      inference('demod', [status(thm)], ['21', '22'])).
% 0.55/0.75  thf(t123_zfmisc_1, axiom,
% 0.55/0.75    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.75     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 0.55/0.75       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.55/0.75  thf('24', plain,
% 0.55/0.75      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.55/0.75         ((k2_zfmisc_1 @ (k3_xboole_0 @ X24 @ X26) @ (k3_xboole_0 @ X25 @ X27))
% 0.55/0.75           = (k3_xboole_0 @ (k2_zfmisc_1 @ X24 @ X25) @ 
% 0.55/0.75              (k2_zfmisc_1 @ X26 @ X27)))),
% 0.55/0.75      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.55/0.75  thf('25', plain,
% 0.55/0.75      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ 
% 0.55/0.75         (k3_xboole_0 @ sk_D_1 @ sk_B)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.55/0.75      inference('demod', [status(thm)], ['23', '24'])).
% 0.55/0.75  thf('26', plain,
% 0.55/0.75      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.55/0.75         ((k2_zfmisc_1 @ (k3_xboole_0 @ X24 @ X26) @ (k3_xboole_0 @ X25 @ X27))
% 0.55/0.75           = (k3_xboole_0 @ (k2_zfmisc_1 @ X24 @ X25) @ 
% 0.55/0.75              (k2_zfmisc_1 @ X26 @ X27)))),
% 0.55/0.75      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.55/0.75  thf('27', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]:
% 0.55/0.75         ((k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ (k3_xboole_0 @ sk_C_1 @ sk_A)) @ 
% 0.55/0.75           (k3_xboole_0 @ X0 @ (k3_xboole_0 @ sk_D_1 @ sk_B)))
% 0.55/0.75           = (k3_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 0.55/0.75              (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.55/0.75      inference('sup+', [status(thm)], ['25', '26'])).
% 0.55/0.75  thf('28', plain,
% 0.55/0.75      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.55/0.75         ((k2_zfmisc_1 @ (k3_xboole_0 @ X24 @ X26) @ (k3_xboole_0 @ X25 @ X27))
% 0.55/0.75           = (k3_xboole_0 @ (k2_zfmisc_1 @ X24 @ X25) @ 
% 0.55/0.75              (k2_zfmisc_1 @ X26 @ X27)))),
% 0.55/0.75      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.55/0.75  thf('29', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]:
% 0.55/0.75         ((k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ (k3_xboole_0 @ sk_C_1 @ sk_A)) @ 
% 0.55/0.75           (k3_xboole_0 @ X0 @ (k3_xboole_0 @ sk_D_1 @ sk_B)))
% 0.55/0.75           = (k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ sk_A) @ 
% 0.55/0.75              (k3_xboole_0 @ X0 @ sk_B)))),
% 0.55/0.75      inference('demod', [status(thm)], ['27', '28'])).
% 0.55/0.75  thf('30', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ 
% 0.55/0.75           (k3_xboole_0 @ X0 @ (k3_xboole_0 @ sk_D_1 @ sk_B)))
% 0.55/0.75           = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_A) @ 
% 0.55/0.75              (k3_xboole_0 @ X0 @ sk_B)))),
% 0.55/0.75      inference('sup+', [status(thm)], ['18', '29'])).
% 0.55/0.75  thf('31', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.55/0.75      inference('sup-', [status(thm)], ['5', '6'])).
% 0.55/0.75  thf('32', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ 
% 0.55/0.75           (k3_xboole_0 @ X0 @ (k3_xboole_0 @ sk_D_1 @ sk_B)))
% 0.55/0.75           = (k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)))),
% 0.55/0.75      inference('demod', [status(thm)], ['30', '31'])).
% 0.55/0.75  thf('33', plain,
% 0.55/0.75      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ 
% 0.55/0.75         (k3_xboole_0 @ sk_D_1 @ sk_B))
% 0.55/0.75         = (k2_zfmisc_1 @ sk_A @ 
% 0.55/0.75            (k3_xboole_0 @ (k3_xboole_0 @ sk_D_1 @ sk_B) @ sk_B)))),
% 0.55/0.75      inference('sup+', [status(thm)], ['7', '32'])).
% 0.55/0.75  thf('34', plain,
% 0.55/0.75      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ 
% 0.55/0.75         (k3_xboole_0 @ sk_D_1 @ sk_B)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.55/0.75      inference('demod', [status(thm)], ['23', '24'])).
% 0.55/0.75  thf('35', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.55/0.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.55/0.75  thf('36', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.55/0.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.55/0.75  thf('37', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.55/0.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.55/0.75  thf('38', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.55/0.75      inference('simplify', [status(thm)], ['13'])).
% 0.55/0.75  thf('39', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.55/0.75      inference('sup+', [status(thm)], ['37', '38'])).
% 0.55/0.75  thf('40', plain,
% 0.55/0.75      (![X12 : $i, X13 : $i]:
% 0.55/0.75         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.55/0.75      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.55/0.75  thf('41', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]:
% 0.55/0.75         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 0.55/0.75           = (k3_xboole_0 @ X0 @ X1))),
% 0.55/0.75      inference('sup-', [status(thm)], ['39', '40'])).
% 0.55/0.75  thf('42', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.55/0.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.55/0.75  thf('43', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]:
% 0.55/0.75         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.55/0.75           = (k3_xboole_0 @ X0 @ X1))),
% 0.55/0.75      inference('demod', [status(thm)], ['41', '42'])).
% 0.55/0.75  thf('44', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]:
% 0.55/0.75         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.55/0.75           = (k3_xboole_0 @ X0 @ X1))),
% 0.55/0.75      inference('sup+', [status(thm)], ['36', '43'])).
% 0.55/0.75  thf('45', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.55/0.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.55/0.75  thf('46', plain,
% 0.55/0.75      (((k2_zfmisc_1 @ sk_A @ sk_B)
% 0.55/0.75         = (k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_D_1 @ sk_B)))),
% 0.55/0.75      inference('demod', [status(thm)], ['33', '34', '35', '44', '45'])).
% 0.55/0.75  thf(t117_zfmisc_1, axiom,
% 0.55/0.75    (![A:$i,B:$i,C:$i]:
% 0.55/0.75     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.55/0.75          ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) ) | 
% 0.55/0.75            ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 0.55/0.75          ( ~( r1_tarski @ B @ C ) ) ) ))).
% 0.55/0.75  thf('47', plain,
% 0.55/0.75      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.55/0.75         (((X17) = (k1_xboole_0))
% 0.55/0.75          | (r1_tarski @ X18 @ X19)
% 0.55/0.75          | ~ (r1_tarski @ (k2_zfmisc_1 @ X17 @ X18) @ 
% 0.55/0.75               (k2_zfmisc_1 @ X17 @ X19)))),
% 0.55/0.75      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 0.55/0.75  thf('48', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ X0) @ 
% 0.55/0.75             (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.55/0.75          | (r1_tarski @ X0 @ (k3_xboole_0 @ sk_D_1 @ sk_B))
% 0.55/0.75          | ((sk_A) = (k1_xboole_0)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['46', '47'])).
% 0.55/0.75  thf('49', plain,
% 0.55/0.75      ((((sk_A) = (k1_xboole_0))
% 0.55/0.75        | (r1_tarski @ sk_B @ (k3_xboole_0 @ sk_D_1 @ sk_B)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['4', '48'])).
% 0.55/0.75  thf('50', plain,
% 0.55/0.75      (![X12 : $i, X13 : $i]:
% 0.55/0.75         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.55/0.75      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.55/0.75  thf('51', plain,
% 0.55/0.75      ((((sk_A) = (k1_xboole_0))
% 0.55/0.75        | ((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_D_1 @ sk_B)) = (sk_B)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['49', '50'])).
% 0.55/0.75  thf('52', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]:
% 0.55/0.75         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.55/0.75           = (k3_xboole_0 @ X0 @ X1))),
% 0.55/0.75      inference('sup+', [status(thm)], ['36', '43'])).
% 0.55/0.75  thf('53', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.55/0.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.55/0.75  thf('54', plain,
% 0.55/0.75      ((((sk_A) = (k1_xboole_0)) | ((k3_xboole_0 @ sk_D_1 @ sk_B) = (sk_B)))),
% 0.55/0.75      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.55/0.75  thf('55', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.55/0.75      inference('sup+', [status(thm)], ['37', '38'])).
% 0.55/0.75  thf('56', plain, (((r1_tarski @ sk_B @ sk_D_1) | ((sk_A) = (k1_xboole_0)))),
% 0.55/0.75      inference('sup+', [status(thm)], ['54', '55'])).
% 0.55/0.75  thf('57', plain,
% 0.55/0.75      ((~ (r1_tarski @ sk_A @ sk_C_1) | ~ (r1_tarski @ sk_B @ sk_D_1))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('58', plain,
% 0.55/0.75      ((~ (r1_tarski @ sk_B @ sk_D_1)) <= (~ ((r1_tarski @ sk_B @ sk_D_1)))),
% 0.55/0.75      inference('split', [status(esa)], ['57'])).
% 0.55/0.75  thf('59', plain,
% 0.55/0.75      (((k2_zfmisc_1 @ sk_A @ sk_B)
% 0.55/0.75         = (k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_D_1 @ sk_B)))),
% 0.55/0.75      inference('demod', [status(thm)], ['33', '34', '35', '44', '45'])).
% 0.55/0.75  thf('60', plain,
% 0.55/0.75      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ 
% 0.55/0.75         (k3_xboole_0 @ sk_D_1 @ sk_B)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.55/0.75      inference('demod', [status(thm)], ['23', '24'])).
% 0.55/0.75  thf('61', plain,
% 0.55/0.75      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.55/0.75         (((X17) = (k1_xboole_0))
% 0.55/0.75          | (r1_tarski @ X18 @ X19)
% 0.55/0.75          | ~ (r1_tarski @ (k2_zfmisc_1 @ X18 @ X17) @ 
% 0.55/0.75               (k2_zfmisc_1 @ X19 @ X17)))),
% 0.55/0.75      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 0.55/0.75  thf('62', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         (~ (r1_tarski @ (k2_zfmisc_1 @ X0 @ (k3_xboole_0 @ sk_D_1 @ sk_B)) @ 
% 0.55/0.75             (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.55/0.75          | (r1_tarski @ X0 @ (k3_xboole_0 @ sk_C_1 @ sk_A))
% 0.55/0.75          | ((k3_xboole_0 @ sk_D_1 @ sk_B) = (k1_xboole_0)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['60', '61'])).
% 0.55/0.75  thf('63', plain,
% 0.55/0.75      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.55/0.75           (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.55/0.75        | ((k3_xboole_0 @ sk_D_1 @ sk_B) = (k1_xboole_0))
% 0.55/0.75        | (r1_tarski @ sk_A @ (k3_xboole_0 @ sk_C_1 @ sk_A)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['59', '62'])).
% 0.55/0.75  thf('64', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.55/0.75      inference('simplify', [status(thm)], ['3'])).
% 0.55/0.75  thf('65', plain,
% 0.55/0.75      ((((k3_xboole_0 @ sk_D_1 @ sk_B) = (k1_xboole_0))
% 0.55/0.75        | (r1_tarski @ sk_A @ (k3_xboole_0 @ sk_C_1 @ sk_A)))),
% 0.55/0.75      inference('demod', [status(thm)], ['63', '64'])).
% 0.55/0.75  thf('66', plain,
% 0.55/0.75      (![X12 : $i, X13 : $i]:
% 0.55/0.75         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.55/0.75      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.55/0.75  thf('67', plain,
% 0.55/0.75      ((((k3_xboole_0 @ sk_D_1 @ sk_B) = (k1_xboole_0))
% 0.55/0.75        | ((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_C_1 @ sk_A)) = (sk_A)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['65', '66'])).
% 0.55/0.75  thf('68', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]:
% 0.55/0.75         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.55/0.75           = (k3_xboole_0 @ X0 @ X1))),
% 0.55/0.75      inference('sup+', [status(thm)], ['36', '43'])).
% 0.55/0.75  thf('69', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.55/0.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.55/0.75  thf('70', plain,
% 0.55/0.75      ((((k3_xboole_0 @ sk_D_1 @ sk_B) = (k1_xboole_0))
% 0.55/0.75        | ((k3_xboole_0 @ sk_C_1 @ sk_A) = (sk_A)))),
% 0.55/0.75      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.55/0.75  thf('71', plain,
% 0.55/0.75      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ 
% 0.55/0.75         (k3_xboole_0 @ sk_D_1 @ sk_B)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.55/0.75      inference('demod', [status(thm)], ['23', '24'])).
% 0.55/0.75  thf('72', plain,
% 0.55/0.75      ((((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ k1_xboole_0)
% 0.55/0.75          = (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.55/0.75        | ((k3_xboole_0 @ sk_C_1 @ sk_A) = (sk_A)))),
% 0.55/0.75      inference('sup+', [status(thm)], ['70', '71'])).
% 0.55/0.75  thf(t113_zfmisc_1, axiom,
% 0.55/0.75    (![A:$i,B:$i]:
% 0.55/0.75     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.55/0.75       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.55/0.75  thf('73', plain,
% 0.55/0.75      (![X15 : $i, X16 : $i]:
% 0.55/0.75         (((k2_zfmisc_1 @ X15 @ X16) = (k1_xboole_0))
% 0.55/0.75          | ((X16) != (k1_xboole_0)))),
% 0.55/0.75      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.55/0.75  thf('74', plain,
% 0.55/0.75      (![X15 : $i]: ((k2_zfmisc_1 @ X15 @ k1_xboole_0) = (k1_xboole_0))),
% 0.55/0.75      inference('simplify', [status(thm)], ['73'])).
% 0.55/0.75  thf('75', plain,
% 0.55/0.75      ((((k1_xboole_0) = (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.55/0.75        | ((k3_xboole_0 @ sk_C_1 @ sk_A) = (sk_A)))),
% 0.55/0.75      inference('demod', [status(thm)], ['72', '74'])).
% 0.55/0.75  thf('76', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('77', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (sk_A))),
% 0.55/0.75      inference('simplify_reflect-', [status(thm)], ['75', '76'])).
% 0.55/0.75  thf('78', plain,
% 0.55/0.75      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.55/0.75      inference('sup+', [status(thm)], ['37', '38'])).
% 0.55/0.75  thf('79', plain, ((r1_tarski @ sk_A @ sk_C_1)),
% 0.55/0.75      inference('sup+', [status(thm)], ['77', '78'])).
% 0.55/0.75  thf('80', plain,
% 0.55/0.75      ((~ (r1_tarski @ sk_A @ sk_C_1)) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 0.55/0.75      inference('split', [status(esa)], ['57'])).
% 0.55/0.75  thf('81', plain, (((r1_tarski @ sk_A @ sk_C_1))),
% 0.55/0.75      inference('sup-', [status(thm)], ['79', '80'])).
% 0.55/0.75  thf('82', plain,
% 0.55/0.75      (~ ((r1_tarski @ sk_B @ sk_D_1)) | ~ ((r1_tarski @ sk_A @ sk_C_1))),
% 0.55/0.75      inference('split', [status(esa)], ['57'])).
% 0.55/0.75  thf('83', plain, (~ ((r1_tarski @ sk_B @ sk_D_1))),
% 0.55/0.75      inference('sat_resolution*', [status(thm)], ['81', '82'])).
% 0.55/0.75  thf('84', plain, (~ (r1_tarski @ sk_B @ sk_D_1)),
% 0.55/0.75      inference('simpl_trail', [status(thm)], ['58', '83'])).
% 0.55/0.75  thf('85', plain, (((sk_A) = (k1_xboole_0))),
% 0.55/0.75      inference('clc', [status(thm)], ['56', '84'])).
% 0.55/0.75  thf('86', plain,
% 0.55/0.75      (![X15 : $i, X16 : $i]:
% 0.55/0.75         (((k2_zfmisc_1 @ X15 @ X16) = (k1_xboole_0))
% 0.55/0.75          | ((X15) != (k1_xboole_0)))),
% 0.55/0.75      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.55/0.75  thf('87', plain,
% 0.55/0.75      (![X16 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X16) = (k1_xboole_0))),
% 0.55/0.75      inference('simplify', [status(thm)], ['86'])).
% 0.55/0.75  thf('88', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.55/0.75      inference('demod', [status(thm)], ['0', '85', '87'])).
% 0.55/0.75  thf('89', plain, ($false), inference('simplify', [status(thm)], ['88'])).
% 0.55/0.75  
% 0.55/0.75  % SZS output end Refutation
% 0.55/0.75  
% 0.55/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
