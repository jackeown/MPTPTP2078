%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.y8bM8kUMpe

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:30 EST 2020

% Result     : Theorem 2.35s
% Output     : Refutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 170 expanded)
%              Number of leaves         :   21 (  62 expanded)
%              Depth                    :   31
%              Number of atoms          :  712 (1274 expanded)
%              Number of equality atoms :   37 (  62 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t149_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ C )
        & ( r1_xboole_0 @ C @ B ) )
     => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ C )
          & ( r1_xboole_0 @ C @ B ) )
       => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t149_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('6',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('7',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X25 ) @ X26 )
      | ( r2_hidden @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k4_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('16',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k4_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('17',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C_1 )
    = sk_B ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('18',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( r1_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k4_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C_1 @ sk_C_1 )
      = ( k3_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k4_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('29',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_B )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('31',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_C_1 )
    = ( k3_xboole_0 @ sk_C_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('33',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_C_1 )
    = ( k3_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
      = ( k3_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('39',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('40',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ X0 ) ),
    inference('sup+',[status(thm)],['34','43'])).

thf('45',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k4_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    r2_hidden @ sk_D @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('58',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D @ ( k4_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,
    ( ( k1_tarski @ sk_D )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['11','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('63',plain,
    ( ( k1_tarski @ sk_D )
    = ( k3_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_D ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_tarski @ sk_D ) )
      | ( r1_tarski @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['6','65'])).

thf('67',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_B )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('68',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('72',plain,(
    r1_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k4_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('74',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('76',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['74','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('80',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference('sup+',[status(thm)],['78','81'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('83',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) )
      | ~ ( r1_xboole_0 @ X15 @ X16 )
      | ~ ( r1_xboole_0 @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','84'])).

thf('86',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('87',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    $false ),
    inference(demod,[status(thm)],['0','87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.y8bM8kUMpe
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:02:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.35/2.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.35/2.56  % Solved by: fo/fo7.sh
% 2.35/2.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.35/2.56  % done 3821 iterations in 2.100s
% 2.35/2.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.35/2.56  % SZS output start Refutation
% 2.35/2.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.35/2.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.35/2.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.35/2.56  thf(sk_A_type, type, sk_A: $i).
% 2.35/2.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.35/2.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.35/2.56  thf(sk_D_type, type, sk_D: $i).
% 2.35/2.56  thf(sk_B_type, type, sk_B: $i).
% 2.35/2.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.35/2.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.35/2.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.35/2.56  thf(t149_zfmisc_1, conjecture,
% 2.35/2.56    (![A:$i,B:$i,C:$i,D:$i]:
% 2.35/2.56     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 2.35/2.56         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 2.35/2.56       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 2.35/2.56  thf(zf_stmt_0, negated_conjecture,
% 2.35/2.56    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 2.35/2.56        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 2.35/2.56            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 2.35/2.56          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 2.35/2.56    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 2.35/2.56  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 2.35/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.56  thf('1', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 2.35/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.56  thf(symmetry_r1_xboole_0, axiom,
% 2.35/2.56    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 2.35/2.56  thf('2', plain,
% 2.35/2.56      (![X2 : $i, X3 : $i]:
% 2.35/2.56         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 2.35/2.56      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.35/2.56  thf('3', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 2.35/2.56      inference('sup-', [status(thm)], ['1', '2'])).
% 2.35/2.56  thf('4', plain,
% 2.35/2.56      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 2.35/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.56  thf(commutativity_k3_xboole_0, axiom,
% 2.35/2.56    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.35/2.56  thf('5', plain,
% 2.35/2.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.35/2.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.35/2.56  thf('6', plain,
% 2.35/2.56      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 2.35/2.56      inference('demod', [status(thm)], ['4', '5'])).
% 2.35/2.56  thf(l27_zfmisc_1, axiom,
% 2.35/2.56    (![A:$i,B:$i]:
% 2.35/2.56     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 2.35/2.56  thf('7', plain,
% 2.35/2.56      (![X25 : $i, X26 : $i]:
% 2.35/2.56         ((r1_xboole_0 @ (k1_tarski @ X25) @ X26) | (r2_hidden @ X25 @ X26))),
% 2.35/2.56      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 2.35/2.56  thf(t83_xboole_1, axiom,
% 2.35/2.56    (![A:$i,B:$i]:
% 2.35/2.56     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.35/2.56  thf('8', plain,
% 2.35/2.56      (![X19 : $i, X20 : $i]:
% 2.35/2.56         (((k4_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_xboole_0 @ X19 @ X20))),
% 2.35/2.56      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.35/2.56  thf('9', plain,
% 2.35/2.56      (![X0 : $i, X1 : $i]:
% 2.35/2.56         ((r2_hidden @ X1 @ X0)
% 2.35/2.56          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 2.35/2.56      inference('sup-', [status(thm)], ['7', '8'])).
% 2.35/2.56  thf(t48_xboole_1, axiom,
% 2.35/2.56    (![A:$i,B:$i]:
% 2.35/2.56     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.35/2.56  thf('10', plain,
% 2.35/2.56      (![X13 : $i, X14 : $i]:
% 2.35/2.56         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 2.35/2.56           = (k3_xboole_0 @ X13 @ X14))),
% 2.35/2.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.35/2.56  thf('11', plain,
% 2.35/2.56      (![X0 : $i, X1 : $i]:
% 2.35/2.56         (((k1_tarski @ X0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 2.35/2.56          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 2.35/2.56      inference('sup+', [status(thm)], ['9', '10'])).
% 2.35/2.56  thf('12', plain,
% 2.35/2.56      (![X13 : $i, X14 : $i]:
% 2.35/2.56         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 2.35/2.56           = (k3_xboole_0 @ X13 @ X14))),
% 2.35/2.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.35/2.56  thf(t36_xboole_1, axiom,
% 2.35/2.56    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 2.35/2.56  thf('13', plain,
% 2.35/2.56      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 2.35/2.56      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.35/2.56  thf('14', plain,
% 2.35/2.56      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 2.35/2.56      inference('sup+', [status(thm)], ['12', '13'])).
% 2.35/2.56  thf('15', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 2.35/2.56      inference('sup-', [status(thm)], ['1', '2'])).
% 2.35/2.56  thf('16', plain,
% 2.35/2.56      (![X19 : $i, X20 : $i]:
% 2.35/2.56         (((k4_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_xboole_0 @ X19 @ X20))),
% 2.35/2.56      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.35/2.56  thf('17', plain, (((k4_xboole_0 @ sk_B @ sk_C_1) = (sk_B))),
% 2.35/2.56      inference('sup-', [status(thm)], ['15', '16'])).
% 2.35/2.56  thf(t106_xboole_1, axiom,
% 2.35/2.56    (![A:$i,B:$i,C:$i]:
% 2.35/2.56     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 2.35/2.56       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 2.35/2.56  thf('18', plain,
% 2.35/2.56      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.35/2.56         ((r1_xboole_0 @ X8 @ X10)
% 2.35/2.56          | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X10)))),
% 2.35/2.56      inference('cnf', [status(esa)], [t106_xboole_1])).
% 2.35/2.56  thf('19', plain,
% 2.35/2.56      (![X0 : $i]: (~ (r1_tarski @ X0 @ sk_B) | (r1_xboole_0 @ X0 @ sk_C_1))),
% 2.35/2.56      inference('sup-', [status(thm)], ['17', '18'])).
% 2.35/2.56  thf('20', plain,
% 2.35/2.56      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ X0) @ sk_C_1)),
% 2.35/2.56      inference('sup-', [status(thm)], ['14', '19'])).
% 2.35/2.56  thf('21', plain,
% 2.35/2.56      (![X2 : $i, X3 : $i]:
% 2.35/2.56         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 2.35/2.56      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.35/2.56  thf('22', plain,
% 2.35/2.56      (![X0 : $i]: (r1_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ sk_B @ X0))),
% 2.35/2.56      inference('sup-', [status(thm)], ['20', '21'])).
% 2.35/2.56  thf('23', plain,
% 2.35/2.56      (![X19 : $i, X20 : $i]:
% 2.35/2.56         (((k4_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_xboole_0 @ X19 @ X20))),
% 2.35/2.56      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.35/2.56  thf('24', plain,
% 2.35/2.56      (![X0 : $i]:
% 2.35/2.56         ((k4_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ sk_B @ X0)) = (sk_C_1))),
% 2.35/2.56      inference('sup-', [status(thm)], ['22', '23'])).
% 2.35/2.56  thf('25', plain,
% 2.35/2.56      (![X13 : $i, X14 : $i]:
% 2.35/2.56         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 2.35/2.56           = (k3_xboole_0 @ X13 @ X14))),
% 2.35/2.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.35/2.56  thf('26', plain,
% 2.35/2.56      (![X0 : $i]:
% 2.35/2.56         ((k4_xboole_0 @ sk_C_1 @ sk_C_1)
% 2.35/2.56           = (k3_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ sk_B @ X0)))),
% 2.35/2.56      inference('sup+', [status(thm)], ['24', '25'])).
% 2.35/2.56  thf('27', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 2.35/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.56  thf('28', plain,
% 2.35/2.56      (![X19 : $i, X20 : $i]:
% 2.35/2.56         (((k4_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_xboole_0 @ X19 @ X20))),
% 2.35/2.56      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.35/2.56  thf('29', plain, (((k4_xboole_0 @ sk_C_1 @ sk_B) = (sk_C_1))),
% 2.35/2.56      inference('sup-', [status(thm)], ['27', '28'])).
% 2.35/2.56  thf('30', plain,
% 2.35/2.56      (![X13 : $i, X14 : $i]:
% 2.35/2.56         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 2.35/2.56           = (k3_xboole_0 @ X13 @ X14))),
% 2.35/2.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.35/2.56  thf('31', plain,
% 2.35/2.56      (((k4_xboole_0 @ sk_C_1 @ sk_C_1) = (k3_xboole_0 @ sk_C_1 @ sk_B))),
% 2.35/2.56      inference('sup+', [status(thm)], ['29', '30'])).
% 2.35/2.56  thf('32', plain,
% 2.35/2.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.35/2.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.35/2.56  thf('33', plain,
% 2.35/2.56      (((k4_xboole_0 @ sk_C_1 @ sk_C_1) = (k3_xboole_0 @ sk_B @ sk_C_1))),
% 2.35/2.56      inference('demod', [status(thm)], ['31', '32'])).
% 2.35/2.56  thf('34', plain,
% 2.35/2.56      (![X0 : $i]:
% 2.35/2.56         ((k3_xboole_0 @ sk_B @ sk_C_1)
% 2.35/2.56           = (k3_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ sk_B @ X0)))),
% 2.35/2.56      inference('demod', [status(thm)], ['26', '33'])).
% 2.35/2.56  thf('35', plain,
% 2.35/2.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.35/2.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.35/2.56  thf('36', plain,
% 2.35/2.56      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 2.35/2.56      inference('sup+', [status(thm)], ['12', '13'])).
% 2.35/2.56  thf('37', plain,
% 2.35/2.56      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 2.35/2.56      inference('sup+', [status(thm)], ['35', '36'])).
% 2.35/2.56  thf('38', plain,
% 2.35/2.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.35/2.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.35/2.56  thf('39', plain,
% 2.35/2.56      (![X13 : $i, X14 : $i]:
% 2.35/2.56         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 2.35/2.56           = (k3_xboole_0 @ X13 @ X14))),
% 2.35/2.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.35/2.56  thf('40', plain,
% 2.35/2.56      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.35/2.56         ((r1_tarski @ X8 @ X9) | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X10)))),
% 2.35/2.56      inference('cnf', [status(esa)], [t106_xboole_1])).
% 2.35/2.56  thf('41', plain,
% 2.35/2.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.35/2.56         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X1))),
% 2.35/2.56      inference('sup-', [status(thm)], ['39', '40'])).
% 2.35/2.56  thf('42', plain,
% 2.35/2.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.35/2.56         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X0))),
% 2.35/2.56      inference('sup-', [status(thm)], ['38', '41'])).
% 2.35/2.56  thf('43', plain,
% 2.35/2.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.35/2.56         (r1_tarski @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0)),
% 2.35/2.56      inference('sup-', [status(thm)], ['37', '42'])).
% 2.35/2.56  thf('44', plain,
% 2.35/2.56      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ sk_B @ sk_C_1) @ X0)),
% 2.35/2.56      inference('sup+', [status(thm)], ['34', '43'])).
% 2.35/2.56  thf('45', plain,
% 2.35/2.56      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.35/2.56         ((r1_xboole_0 @ X8 @ X10)
% 2.35/2.56          | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X10)))),
% 2.35/2.56      inference('cnf', [status(esa)], [t106_xboole_1])).
% 2.35/2.56  thf('46', plain,
% 2.35/2.56      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C_1) @ X0)),
% 2.35/2.56      inference('sup-', [status(thm)], ['44', '45'])).
% 2.35/2.56  thf('47', plain,
% 2.35/2.56      (![X2 : $i, X3 : $i]:
% 2.35/2.56         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 2.35/2.56      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.35/2.56  thf('48', plain,
% 2.35/2.56      (![X0 : $i]: (r1_xboole_0 @ X0 @ (k3_xboole_0 @ sk_B @ sk_C_1))),
% 2.35/2.56      inference('sup-', [status(thm)], ['46', '47'])).
% 2.35/2.56  thf('49', plain,
% 2.35/2.56      (![X19 : $i, X20 : $i]:
% 2.35/2.56         (((k4_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_xboole_0 @ X19 @ X20))),
% 2.35/2.56      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.35/2.56  thf('50', plain,
% 2.35/2.56      (![X0 : $i]: ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ sk_B @ sk_C_1)) = (X0))),
% 2.35/2.56      inference('sup-', [status(thm)], ['48', '49'])).
% 2.35/2.56  thf('51', plain,
% 2.35/2.56      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 2.35/2.56      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.35/2.56  thf('52', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 2.35/2.56      inference('sup+', [status(thm)], ['50', '51'])).
% 2.35/2.56  thf('53', plain,
% 2.35/2.56      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.35/2.56         ((r1_xboole_0 @ X8 @ X10)
% 2.35/2.56          | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X10)))),
% 2.35/2.56      inference('cnf', [status(esa)], [t106_xboole_1])).
% 2.35/2.56  thf('54', plain,
% 2.35/2.56      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 2.35/2.56      inference('sup-', [status(thm)], ['52', '53'])).
% 2.35/2.56  thf('55', plain,
% 2.35/2.56      (![X2 : $i, X3 : $i]:
% 2.35/2.56         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 2.35/2.56      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.35/2.56  thf('56', plain,
% 2.35/2.56      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 2.35/2.56      inference('sup-', [status(thm)], ['54', '55'])).
% 2.35/2.56  thf('57', plain, ((r2_hidden @ sk_D @ sk_C_1)),
% 2.35/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.56  thf(t3_xboole_0, axiom,
% 2.35/2.56    (![A:$i,B:$i]:
% 2.35/2.56     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 2.35/2.56            ( r1_xboole_0 @ A @ B ) ) ) & 
% 2.35/2.56       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 2.35/2.56            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 2.35/2.56  thf('58', plain,
% 2.35/2.56      (![X4 : $i, X6 : $i, X7 : $i]:
% 2.35/2.56         (~ (r2_hidden @ X6 @ X4)
% 2.35/2.56          | ~ (r2_hidden @ X6 @ X7)
% 2.35/2.56          | ~ (r1_xboole_0 @ X4 @ X7))),
% 2.35/2.56      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.35/2.56  thf('59', plain,
% 2.35/2.56      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 2.35/2.56      inference('sup-', [status(thm)], ['57', '58'])).
% 2.35/2.56  thf('60', plain,
% 2.35/2.56      (![X0 : $i]: ~ (r2_hidden @ sk_D @ (k4_xboole_0 @ X0 @ sk_C_1))),
% 2.35/2.56      inference('sup-', [status(thm)], ['56', '59'])).
% 2.35/2.56  thf('61', plain,
% 2.35/2.56      (((k1_tarski @ sk_D) = (k3_xboole_0 @ (k1_tarski @ sk_D) @ sk_C_1))),
% 2.35/2.56      inference('sup-', [status(thm)], ['11', '60'])).
% 2.35/2.56  thf('62', plain,
% 2.35/2.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.35/2.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.35/2.56  thf('63', plain,
% 2.35/2.56      (((k1_tarski @ sk_D) = (k3_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_D)))),
% 2.35/2.56      inference('demod', [status(thm)], ['61', '62'])).
% 2.35/2.56  thf('64', plain,
% 2.35/2.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.35/2.56         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X1))),
% 2.35/2.56      inference('sup-', [status(thm)], ['39', '40'])).
% 2.35/2.56  thf('65', plain,
% 2.35/2.56      (![X0 : $i]:
% 2.35/2.56         (~ (r1_tarski @ X0 @ (k1_tarski @ sk_D)) | (r1_tarski @ X0 @ sk_C_1))),
% 2.35/2.56      inference('sup-', [status(thm)], ['63', '64'])).
% 2.35/2.56  thf('66', plain, ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_C_1)),
% 2.35/2.56      inference('sup-', [status(thm)], ['6', '65'])).
% 2.35/2.56  thf('67', plain, (((k4_xboole_0 @ sk_C_1 @ sk_B) = (sk_C_1))),
% 2.35/2.56      inference('sup-', [status(thm)], ['27', '28'])).
% 2.35/2.56  thf('68', plain,
% 2.35/2.56      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.35/2.56         ((r1_xboole_0 @ X8 @ X10)
% 2.35/2.56          | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X10)))),
% 2.35/2.56      inference('cnf', [status(esa)], [t106_xboole_1])).
% 2.35/2.56  thf('69', plain,
% 2.35/2.56      (![X0 : $i]: (~ (r1_tarski @ X0 @ sk_C_1) | (r1_xboole_0 @ X0 @ sk_B))),
% 2.35/2.56      inference('sup-', [status(thm)], ['67', '68'])).
% 2.35/2.56  thf('70', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_B)),
% 2.35/2.56      inference('sup-', [status(thm)], ['66', '69'])).
% 2.35/2.56  thf('71', plain,
% 2.35/2.56      (![X2 : $i, X3 : $i]:
% 2.35/2.56         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 2.35/2.56      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.35/2.56  thf('72', plain, ((r1_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_A))),
% 2.35/2.56      inference('sup-', [status(thm)], ['70', '71'])).
% 2.35/2.56  thf('73', plain,
% 2.35/2.56      (![X19 : $i, X20 : $i]:
% 2.35/2.56         (((k4_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_xboole_0 @ X19 @ X20))),
% 2.35/2.56      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.35/2.56  thf('74', plain,
% 2.35/2.56      (((k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_A)) = (sk_B))),
% 2.35/2.56      inference('sup-', [status(thm)], ['72', '73'])).
% 2.35/2.56  thf('75', plain,
% 2.35/2.56      (![X13 : $i, X14 : $i]:
% 2.35/2.56         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 2.35/2.56           = (k3_xboole_0 @ X13 @ X14))),
% 2.35/2.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.35/2.56  thf('76', plain,
% 2.35/2.56      (![X13 : $i, X14 : $i]:
% 2.35/2.56         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 2.35/2.56           = (k3_xboole_0 @ X13 @ X14))),
% 2.35/2.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.35/2.56  thf('77', plain,
% 2.35/2.56      (![X0 : $i, X1 : $i]:
% 2.35/2.56         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 2.35/2.56           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.35/2.56      inference('sup+', [status(thm)], ['75', '76'])).
% 2.35/2.56  thf('78', plain,
% 2.35/2.56      (((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_A)) = (sk_B))),
% 2.35/2.56      inference('demod', [status(thm)], ['74', '77'])).
% 2.35/2.56  thf('79', plain,
% 2.35/2.56      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 2.35/2.56      inference('sup+', [status(thm)], ['35', '36'])).
% 2.35/2.56  thf('80', plain,
% 2.35/2.56      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.35/2.56         ((r1_xboole_0 @ X8 @ X10)
% 2.35/2.56          | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X10)))),
% 2.35/2.56      inference('cnf', [status(esa)], [t106_xboole_1])).
% 2.35/2.56  thf('81', plain,
% 2.35/2.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.35/2.56         (r1_xboole_0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0)),
% 2.35/2.56      inference('sup-', [status(thm)], ['79', '80'])).
% 2.35/2.56  thf('82', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 2.35/2.56      inference('sup+', [status(thm)], ['78', '81'])).
% 2.35/2.56  thf(t70_xboole_1, axiom,
% 2.35/2.56    (![A:$i,B:$i,C:$i]:
% 2.35/2.56     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 2.35/2.56            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 2.35/2.56       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 2.35/2.56            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 2.35/2.56  thf('83', plain,
% 2.35/2.56      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.35/2.56         ((r1_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17))
% 2.35/2.56          | ~ (r1_xboole_0 @ X15 @ X16)
% 2.35/2.56          | ~ (r1_xboole_0 @ X15 @ X17))),
% 2.35/2.56      inference('cnf', [status(esa)], [t70_xboole_1])).
% 2.35/2.56  thf('84', plain,
% 2.35/2.56      (![X0 : $i]:
% 2.35/2.56         (~ (r1_xboole_0 @ sk_B @ X0)
% 2.35/2.56          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 2.35/2.56      inference('sup-', [status(thm)], ['82', '83'])).
% 2.35/2.56  thf('85', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_1))),
% 2.35/2.56      inference('sup-', [status(thm)], ['3', '84'])).
% 2.35/2.56  thf('86', plain,
% 2.35/2.56      (![X2 : $i, X3 : $i]:
% 2.35/2.56         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 2.35/2.56      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.35/2.56  thf('87', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 2.35/2.56      inference('sup-', [status(thm)], ['85', '86'])).
% 2.35/2.56  thf('88', plain, ($false), inference('demod', [status(thm)], ['0', '87'])).
% 2.35/2.56  
% 2.35/2.56  % SZS output end Refutation
% 2.35/2.56  
% 2.35/2.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
