%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aZUDIUpDWH

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:52 EST 2020

% Result     : Theorem 1.10s
% Output     : Refutation 1.10s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 148 expanded)
%              Number of leaves         :   22 (  53 expanded)
%              Depth                    :   12
%              Number of atoms          :  611 (1150 expanded)
%              Number of equality atoms :   19 (  47 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t31_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( r1_tarski @ A @ B )
             => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X55: $i] :
      ( ( ( k3_relat_1 @ X55 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X55 ) @ ( k2_relat_1 @ X55 ) ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X36 @ X37 ) )
      = ( k2_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('3',plain,(
    ! [X55: $i] :
      ( ( ( k3_relat_1 @ X55 )
        = ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ X55 ) @ ( k2_relat_1 @ X55 ) ) ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ( X12 != X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,(
    ! [X13: $i] :
      ( r1_tarski @ X13 @ X13 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_tarski @ X15 @ ( k2_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('7',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X36 @ X37 ) )
      = ( k2_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('8',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_tarski @ X15 @ ( k3_tarski @ ( k2_tarski @ X17 @ X16 ) ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','9'])).

thf('11',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( v1_relat_1 @ X58 )
      | ( r1_tarski @ ( k2_relat_1 @ X59 ) @ ( k2_relat_1 @ X58 ) )
      | ~ ( r1_tarski @ X59 @ X58 )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('17',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X19 @ X20 )
      | ~ ( r1_tarski @ X20 @ X21 )
      | ( r1_tarski @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X55: $i] :
      ( ( ( k3_relat_1 @ X55 )
        = ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ X55 ) @ ( k2_relat_1 @ X55 ) ) ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('23',plain,(
    ! [X13: $i] :
      ( r1_tarski @ X13 @ X13 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('24',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X25 @ X26 ) @ X27 )
      | ~ ( r1_tarski @ X25 @ ( k2_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('25',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X36 @ X37 ) )
      = ( k2_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('26',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X25 @ X26 ) @ X27 )
      | ~ ( r1_tarski @ X25 @ ( k3_tarski @ ( k2_tarski @ X26 @ X27 ) ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ ( k3_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X19 @ X20 )
      | ~ ( r1_tarski @ X20 @ X21 )
      | ( r1_tarski @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k3_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) @ X1 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ ( k3_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k3_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('34',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( r1_tarski @ X28 @ ( k2_xboole_0 @ X29 @ X30 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X28 @ X29 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('35',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X36 @ X37 ) )
      = ( k2_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('36',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( r1_tarski @ X28 @ ( k3_tarski @ ( k2_tarski @ X29 @ X30 ) ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X28 @ X29 ) @ X30 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('38',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k2_tarski @ X35 @ X34 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('39',plain,(
    ! [X55: $i] :
      ( ( ( k3_relat_1 @ X55 )
        = ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ X55 ) @ ( k2_relat_1 @ X55 ) ) ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('40',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k2_tarski @ X35 @ X34 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('44',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( v1_relat_1 @ X58 )
      | ( r1_tarski @ ( k1_relat_1 @ X59 ) @ ( k1_relat_1 @ X58 ) )
      | ~ ( r1_tarski @ X59 @ X58 )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X19 @ X20 )
      | ~ ( r1_tarski @ X20 @ X21 )
      | ( r1_tarski @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X13: $i] :
      ( r1_tarski @ X13 @ X13 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('56',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ X31 @ X32 )
      | ~ ( r1_tarski @ X33 @ X32 )
      | ( r1_tarski @ ( k2_xboole_0 @ X31 @ X33 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('57',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X36 @ X37 ) )
      = ( k2_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('58',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ X31 @ X32 )
      | ~ ( r1_tarski @ X33 @ X32 )
      | ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X31 @ X33 ) ) @ X32 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    r1_tarski @ ( k3_tarski @ ( k2_tarski @ ( k3_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ) ) @ ( k3_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['54','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('62',plain,(
    ! [X12: $i,X14: $i] :
      ( ( X12 = X14 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) @ X1 )
      | ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k3_tarski @ ( k2_tarski @ ( k3_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ) )
    = ( k3_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['37','38','64'])).

thf('66',plain,(
    $false ),
    inference(demod,[status(thm)],['0','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aZUDIUpDWH
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:21:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.10/1.29  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.10/1.29  % Solved by: fo/fo7.sh
% 1.10/1.29  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.10/1.29  % done 1711 iterations in 0.840s
% 1.10/1.29  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.10/1.29  % SZS output start Refutation
% 1.10/1.29  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.10/1.29  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 1.10/1.29  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.10/1.29  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.10/1.29  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.10/1.29  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.10/1.29  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.10/1.29  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.10/1.29  thf(sk_B_type, type, sk_B: $i).
% 1.10/1.29  thf(sk_A_type, type, sk_A: $i).
% 1.10/1.29  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.10/1.29  thf(t31_relat_1, conjecture,
% 1.10/1.29    (![A:$i]:
% 1.10/1.29     ( ( v1_relat_1 @ A ) =>
% 1.10/1.29       ( ![B:$i]:
% 1.10/1.29         ( ( v1_relat_1 @ B ) =>
% 1.10/1.29           ( ( r1_tarski @ A @ B ) =>
% 1.10/1.29             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 1.10/1.29  thf(zf_stmt_0, negated_conjecture,
% 1.10/1.29    (~( ![A:$i]:
% 1.10/1.29        ( ( v1_relat_1 @ A ) =>
% 1.10/1.29          ( ![B:$i]:
% 1.10/1.29            ( ( v1_relat_1 @ B ) =>
% 1.10/1.29              ( ( r1_tarski @ A @ B ) =>
% 1.10/1.29                ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 1.10/1.29    inference('cnf.neg', [status(esa)], [t31_relat_1])).
% 1.10/1.29  thf('0', plain, (~ (r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 1.10/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.29  thf(d6_relat_1, axiom,
% 1.10/1.29    (![A:$i]:
% 1.10/1.29     ( ( v1_relat_1 @ A ) =>
% 1.10/1.29       ( ( k3_relat_1 @ A ) =
% 1.10/1.29         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 1.10/1.29  thf('1', plain,
% 1.10/1.29      (![X55 : $i]:
% 1.10/1.29         (((k3_relat_1 @ X55)
% 1.10/1.29            = (k2_xboole_0 @ (k1_relat_1 @ X55) @ (k2_relat_1 @ X55)))
% 1.10/1.29          | ~ (v1_relat_1 @ X55))),
% 1.10/1.29      inference('cnf', [status(esa)], [d6_relat_1])).
% 1.10/1.29  thf(l51_zfmisc_1, axiom,
% 1.10/1.29    (![A:$i,B:$i]:
% 1.10/1.29     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.10/1.29  thf('2', plain,
% 1.10/1.29      (![X36 : $i, X37 : $i]:
% 1.10/1.29         ((k3_tarski @ (k2_tarski @ X36 @ X37)) = (k2_xboole_0 @ X36 @ X37))),
% 1.10/1.29      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.10/1.29  thf('3', plain,
% 1.10/1.29      (![X55 : $i]:
% 1.10/1.29         (((k3_relat_1 @ X55)
% 1.10/1.29            = (k3_tarski @ 
% 1.10/1.29               (k2_tarski @ (k1_relat_1 @ X55) @ (k2_relat_1 @ X55))))
% 1.10/1.29          | ~ (v1_relat_1 @ X55))),
% 1.10/1.29      inference('demod', [status(thm)], ['1', '2'])).
% 1.10/1.29  thf(d10_xboole_0, axiom,
% 1.10/1.29    (![A:$i,B:$i]:
% 1.10/1.29     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.10/1.29  thf('4', plain,
% 1.10/1.29      (![X12 : $i, X13 : $i]: ((r1_tarski @ X12 @ X13) | ((X12) != (X13)))),
% 1.10/1.29      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.10/1.29  thf('5', plain, (![X13 : $i]: (r1_tarski @ X13 @ X13)),
% 1.10/1.29      inference('simplify', [status(thm)], ['4'])).
% 1.10/1.29  thf(t10_xboole_1, axiom,
% 1.10/1.29    (![A:$i,B:$i,C:$i]:
% 1.10/1.29     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 1.10/1.29  thf('6', plain,
% 1.10/1.29      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.10/1.29         (~ (r1_tarski @ X15 @ X16)
% 1.10/1.29          | (r1_tarski @ X15 @ (k2_xboole_0 @ X17 @ X16)))),
% 1.10/1.29      inference('cnf', [status(esa)], [t10_xboole_1])).
% 1.10/1.29  thf('7', plain,
% 1.10/1.29      (![X36 : $i, X37 : $i]:
% 1.10/1.29         ((k3_tarski @ (k2_tarski @ X36 @ X37)) = (k2_xboole_0 @ X36 @ X37))),
% 1.10/1.29      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.10/1.29  thf('8', plain,
% 1.10/1.29      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.10/1.29         (~ (r1_tarski @ X15 @ X16)
% 1.10/1.29          | (r1_tarski @ X15 @ (k3_tarski @ (k2_tarski @ X17 @ X16))))),
% 1.10/1.29      inference('demod', [status(thm)], ['6', '7'])).
% 1.10/1.29  thf('9', plain,
% 1.10/1.29      (![X0 : $i, X1 : $i]:
% 1.10/1.29         (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 1.10/1.29      inference('sup-', [status(thm)], ['5', '8'])).
% 1.10/1.29  thf('10', plain,
% 1.10/1.29      (![X0 : $i]:
% 1.10/1.29         ((r1_tarski @ (k2_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 1.10/1.29          | ~ (v1_relat_1 @ X0))),
% 1.10/1.29      inference('sup+', [status(thm)], ['3', '9'])).
% 1.10/1.29  thf('11', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.10/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.29  thf(t25_relat_1, axiom,
% 1.10/1.29    (![A:$i]:
% 1.10/1.29     ( ( v1_relat_1 @ A ) =>
% 1.10/1.29       ( ![B:$i]:
% 1.10/1.29         ( ( v1_relat_1 @ B ) =>
% 1.10/1.29           ( ( r1_tarski @ A @ B ) =>
% 1.10/1.29             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 1.10/1.29               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 1.10/1.29  thf('12', plain,
% 1.10/1.29      (![X58 : $i, X59 : $i]:
% 1.10/1.29         (~ (v1_relat_1 @ X58)
% 1.10/1.29          | (r1_tarski @ (k2_relat_1 @ X59) @ (k2_relat_1 @ X58))
% 1.10/1.29          | ~ (r1_tarski @ X59 @ X58)
% 1.10/1.29          | ~ (v1_relat_1 @ X59))),
% 1.10/1.29      inference('cnf', [status(esa)], [t25_relat_1])).
% 1.10/1.29  thf('13', plain,
% 1.10/1.29      ((~ (v1_relat_1 @ sk_A)
% 1.10/1.29        | (r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))
% 1.10/1.29        | ~ (v1_relat_1 @ sk_B))),
% 1.10/1.29      inference('sup-', [status(thm)], ['11', '12'])).
% 1.10/1.29  thf('14', plain, ((v1_relat_1 @ sk_A)),
% 1.10/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.29  thf('15', plain, ((v1_relat_1 @ sk_B)),
% 1.10/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.29  thf('16', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))),
% 1.10/1.29      inference('demod', [status(thm)], ['13', '14', '15'])).
% 1.10/1.29  thf(t1_xboole_1, axiom,
% 1.10/1.29    (![A:$i,B:$i,C:$i]:
% 1.10/1.29     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.10/1.29       ( r1_tarski @ A @ C ) ))).
% 1.10/1.29  thf('17', plain,
% 1.10/1.29      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.10/1.29         (~ (r1_tarski @ X19 @ X20)
% 1.10/1.29          | ~ (r1_tarski @ X20 @ X21)
% 1.10/1.29          | (r1_tarski @ X19 @ X21))),
% 1.10/1.29      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.10/1.29  thf('18', plain,
% 1.10/1.29      (![X0 : $i]:
% 1.10/1.29         ((r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 1.10/1.29          | ~ (r1_tarski @ (k2_relat_1 @ sk_B) @ X0))),
% 1.10/1.29      inference('sup-', [status(thm)], ['16', '17'])).
% 1.10/1.29  thf('19', plain,
% 1.10/1.29      ((~ (v1_relat_1 @ sk_B)
% 1.10/1.29        | (r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 1.10/1.29      inference('sup-', [status(thm)], ['10', '18'])).
% 1.10/1.29  thf('20', plain, ((v1_relat_1 @ sk_B)),
% 1.10/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.29  thf('21', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 1.10/1.29      inference('demod', [status(thm)], ['19', '20'])).
% 1.10/1.29  thf('22', plain,
% 1.10/1.29      (![X55 : $i]:
% 1.10/1.29         (((k3_relat_1 @ X55)
% 1.10/1.29            = (k3_tarski @ 
% 1.10/1.29               (k2_tarski @ (k1_relat_1 @ X55) @ (k2_relat_1 @ X55))))
% 1.10/1.29          | ~ (v1_relat_1 @ X55))),
% 1.10/1.29      inference('demod', [status(thm)], ['1', '2'])).
% 1.10/1.29  thf('23', plain, (![X13 : $i]: (r1_tarski @ X13 @ X13)),
% 1.10/1.29      inference('simplify', [status(thm)], ['4'])).
% 1.10/1.29  thf(t43_xboole_1, axiom,
% 1.10/1.29    (![A:$i,B:$i,C:$i]:
% 1.10/1.29     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 1.10/1.29       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 1.10/1.29  thf('24', plain,
% 1.10/1.29      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.10/1.29         ((r1_tarski @ (k4_xboole_0 @ X25 @ X26) @ X27)
% 1.10/1.29          | ~ (r1_tarski @ X25 @ (k2_xboole_0 @ X26 @ X27)))),
% 1.10/1.29      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.10/1.29  thf('25', plain,
% 1.10/1.29      (![X36 : $i, X37 : $i]:
% 1.10/1.29         ((k3_tarski @ (k2_tarski @ X36 @ X37)) = (k2_xboole_0 @ X36 @ X37))),
% 1.10/1.29      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.10/1.29  thf('26', plain,
% 1.10/1.29      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.10/1.29         ((r1_tarski @ (k4_xboole_0 @ X25 @ X26) @ X27)
% 1.10/1.29          | ~ (r1_tarski @ X25 @ (k3_tarski @ (k2_tarski @ X26 @ X27))))),
% 1.10/1.29      inference('demod', [status(thm)], ['24', '25'])).
% 1.10/1.29  thf('27', plain,
% 1.10/1.29      (![X0 : $i, X1 : $i]:
% 1.10/1.29         (r1_tarski @ 
% 1.10/1.29          (k4_xboole_0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)) @ X1) @ X0)),
% 1.10/1.29      inference('sup-', [status(thm)], ['23', '26'])).
% 1.10/1.29  thf('28', plain,
% 1.10/1.29      (![X0 : $i]:
% 1.10/1.29         ((r1_tarski @ (k4_xboole_0 @ (k3_relat_1 @ X0) @ (k1_relat_1 @ X0)) @ 
% 1.10/1.29           (k2_relat_1 @ X0))
% 1.10/1.29          | ~ (v1_relat_1 @ X0))),
% 1.10/1.29      inference('sup+', [status(thm)], ['22', '27'])).
% 1.10/1.29  thf('29', plain,
% 1.10/1.29      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.10/1.29         (~ (r1_tarski @ X19 @ X20)
% 1.10/1.29          | ~ (r1_tarski @ X20 @ X21)
% 1.10/1.29          | (r1_tarski @ X19 @ X21))),
% 1.10/1.29      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.10/1.29  thf('30', plain,
% 1.10/1.29      (![X0 : $i, X1 : $i]:
% 1.10/1.29         (~ (v1_relat_1 @ X0)
% 1.10/1.29          | (r1_tarski @ 
% 1.10/1.29             (k4_xboole_0 @ (k3_relat_1 @ X0) @ (k1_relat_1 @ X0)) @ X1)
% 1.10/1.29          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 1.10/1.29      inference('sup-', [status(thm)], ['28', '29'])).
% 1.10/1.29  thf('31', plain,
% 1.10/1.29      (((r1_tarski @ 
% 1.10/1.29         (k4_xboole_0 @ (k3_relat_1 @ sk_A) @ (k1_relat_1 @ sk_A)) @ 
% 1.10/1.29         (k3_relat_1 @ sk_B))
% 1.10/1.29        | ~ (v1_relat_1 @ sk_A))),
% 1.10/1.29      inference('sup-', [status(thm)], ['21', '30'])).
% 1.10/1.29  thf('32', plain, ((v1_relat_1 @ sk_A)),
% 1.10/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.29  thf('33', plain,
% 1.10/1.29      ((r1_tarski @ 
% 1.10/1.29        (k4_xboole_0 @ (k3_relat_1 @ sk_A) @ (k1_relat_1 @ sk_A)) @ 
% 1.10/1.29        (k3_relat_1 @ sk_B))),
% 1.10/1.29      inference('demod', [status(thm)], ['31', '32'])).
% 1.10/1.29  thf(t44_xboole_1, axiom,
% 1.10/1.29    (![A:$i,B:$i,C:$i]:
% 1.10/1.29     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 1.10/1.29       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.10/1.29  thf('34', plain,
% 1.10/1.29      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.10/1.29         ((r1_tarski @ X28 @ (k2_xboole_0 @ X29 @ X30))
% 1.10/1.29          | ~ (r1_tarski @ (k4_xboole_0 @ X28 @ X29) @ X30))),
% 1.10/1.29      inference('cnf', [status(esa)], [t44_xboole_1])).
% 1.10/1.29  thf('35', plain,
% 1.10/1.29      (![X36 : $i, X37 : $i]:
% 1.10/1.29         ((k3_tarski @ (k2_tarski @ X36 @ X37)) = (k2_xboole_0 @ X36 @ X37))),
% 1.10/1.29      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.10/1.29  thf('36', plain,
% 1.10/1.29      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.10/1.29         ((r1_tarski @ X28 @ (k3_tarski @ (k2_tarski @ X29 @ X30)))
% 1.10/1.29          | ~ (r1_tarski @ (k4_xboole_0 @ X28 @ X29) @ X30))),
% 1.10/1.29      inference('demod', [status(thm)], ['34', '35'])).
% 1.10/1.29  thf('37', plain,
% 1.10/1.29      ((r1_tarski @ (k3_relat_1 @ sk_A) @ 
% 1.10/1.29        (k3_tarski @ (k2_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))))),
% 1.10/1.29      inference('sup-', [status(thm)], ['33', '36'])).
% 1.10/1.29  thf(commutativity_k2_tarski, axiom,
% 1.10/1.29    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.10/1.29  thf('38', plain,
% 1.10/1.29      (![X34 : $i, X35 : $i]:
% 1.10/1.29         ((k2_tarski @ X35 @ X34) = (k2_tarski @ X34 @ X35))),
% 1.10/1.29      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.10/1.29  thf('39', plain,
% 1.10/1.29      (![X55 : $i]:
% 1.10/1.29         (((k3_relat_1 @ X55)
% 1.10/1.29            = (k3_tarski @ 
% 1.10/1.29               (k2_tarski @ (k1_relat_1 @ X55) @ (k2_relat_1 @ X55))))
% 1.10/1.29          | ~ (v1_relat_1 @ X55))),
% 1.10/1.29      inference('demod', [status(thm)], ['1', '2'])).
% 1.10/1.29  thf('40', plain,
% 1.10/1.29      (![X34 : $i, X35 : $i]:
% 1.10/1.29         ((k2_tarski @ X35 @ X34) = (k2_tarski @ X34 @ X35))),
% 1.10/1.29      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.10/1.29  thf('41', plain,
% 1.10/1.29      (![X0 : $i, X1 : $i]:
% 1.10/1.29         (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 1.10/1.29      inference('sup-', [status(thm)], ['5', '8'])).
% 1.10/1.29  thf('42', plain,
% 1.10/1.29      (![X0 : $i, X1 : $i]:
% 1.10/1.29         (r1_tarski @ X1 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 1.10/1.29      inference('sup+', [status(thm)], ['40', '41'])).
% 1.10/1.29  thf('43', plain,
% 1.10/1.29      (![X0 : $i]:
% 1.10/1.29         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 1.10/1.29          | ~ (v1_relat_1 @ X0))),
% 1.10/1.29      inference('sup+', [status(thm)], ['39', '42'])).
% 1.10/1.29  thf('44', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.10/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.29  thf('45', plain,
% 1.10/1.29      (![X58 : $i, X59 : $i]:
% 1.10/1.29         (~ (v1_relat_1 @ X58)
% 1.10/1.29          | (r1_tarski @ (k1_relat_1 @ X59) @ (k1_relat_1 @ X58))
% 1.10/1.29          | ~ (r1_tarski @ X59 @ X58)
% 1.10/1.29          | ~ (v1_relat_1 @ X59))),
% 1.10/1.29      inference('cnf', [status(esa)], [t25_relat_1])).
% 1.10/1.29  thf('46', plain,
% 1.10/1.29      ((~ (v1_relat_1 @ sk_A)
% 1.10/1.29        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 1.10/1.29        | ~ (v1_relat_1 @ sk_B))),
% 1.10/1.29      inference('sup-', [status(thm)], ['44', '45'])).
% 1.10/1.29  thf('47', plain, ((v1_relat_1 @ sk_A)),
% 1.10/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.29  thf('48', plain, ((v1_relat_1 @ sk_B)),
% 1.10/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.29  thf('49', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))),
% 1.10/1.29      inference('demod', [status(thm)], ['46', '47', '48'])).
% 1.10/1.29  thf('50', plain,
% 1.10/1.29      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.10/1.29         (~ (r1_tarski @ X19 @ X20)
% 1.10/1.29          | ~ (r1_tarski @ X20 @ X21)
% 1.10/1.29          | (r1_tarski @ X19 @ X21))),
% 1.10/1.29      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.10/1.29  thf('51', plain,
% 1.10/1.29      (![X0 : $i]:
% 1.10/1.29         ((r1_tarski @ (k1_relat_1 @ sk_A) @ X0)
% 1.10/1.29          | ~ (r1_tarski @ (k1_relat_1 @ sk_B) @ X0))),
% 1.10/1.29      inference('sup-', [status(thm)], ['49', '50'])).
% 1.10/1.29  thf('52', plain,
% 1.10/1.29      ((~ (v1_relat_1 @ sk_B)
% 1.10/1.29        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 1.10/1.29      inference('sup-', [status(thm)], ['43', '51'])).
% 1.10/1.29  thf('53', plain, ((v1_relat_1 @ sk_B)),
% 1.10/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.29  thf('54', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 1.10/1.29      inference('demod', [status(thm)], ['52', '53'])).
% 1.10/1.29  thf('55', plain, (![X13 : $i]: (r1_tarski @ X13 @ X13)),
% 1.10/1.29      inference('simplify', [status(thm)], ['4'])).
% 1.10/1.29  thf(t8_xboole_1, axiom,
% 1.10/1.29    (![A:$i,B:$i,C:$i]:
% 1.10/1.29     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 1.10/1.29       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.10/1.29  thf('56', plain,
% 1.10/1.29      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.10/1.29         (~ (r1_tarski @ X31 @ X32)
% 1.10/1.29          | ~ (r1_tarski @ X33 @ X32)
% 1.10/1.29          | (r1_tarski @ (k2_xboole_0 @ X31 @ X33) @ X32))),
% 1.10/1.29      inference('cnf', [status(esa)], [t8_xboole_1])).
% 1.10/1.29  thf('57', plain,
% 1.10/1.29      (![X36 : $i, X37 : $i]:
% 1.10/1.29         ((k3_tarski @ (k2_tarski @ X36 @ X37)) = (k2_xboole_0 @ X36 @ X37))),
% 1.10/1.29      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.10/1.29  thf('58', plain,
% 1.10/1.29      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.10/1.29         (~ (r1_tarski @ X31 @ X32)
% 1.10/1.29          | ~ (r1_tarski @ X33 @ X32)
% 1.10/1.29          | (r1_tarski @ (k3_tarski @ (k2_tarski @ X31 @ X33)) @ X32))),
% 1.10/1.29      inference('demod', [status(thm)], ['56', '57'])).
% 1.10/1.29  thf('59', plain,
% 1.10/1.29      (![X0 : $i, X1 : $i]:
% 1.10/1.29         ((r1_tarski @ (k3_tarski @ (k2_tarski @ X0 @ X1)) @ X0)
% 1.10/1.29          | ~ (r1_tarski @ X1 @ X0))),
% 1.10/1.29      inference('sup-', [status(thm)], ['55', '58'])).
% 1.10/1.29  thf('60', plain,
% 1.10/1.29      ((r1_tarski @ 
% 1.10/1.29        (k3_tarski @ (k2_tarski @ (k3_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A))) @ 
% 1.10/1.29        (k3_relat_1 @ sk_B))),
% 1.10/1.29      inference('sup-', [status(thm)], ['54', '59'])).
% 1.10/1.29  thf('61', plain,
% 1.10/1.29      (![X0 : $i, X1 : $i]:
% 1.10/1.29         (r1_tarski @ X1 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 1.10/1.29      inference('sup+', [status(thm)], ['40', '41'])).
% 1.10/1.29  thf('62', plain,
% 1.10/1.29      (![X12 : $i, X14 : $i]:
% 1.10/1.29         (((X12) = (X14))
% 1.10/1.29          | ~ (r1_tarski @ X14 @ X12)
% 1.10/1.29          | ~ (r1_tarski @ X12 @ X14))),
% 1.10/1.29      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.10/1.29  thf('63', plain,
% 1.10/1.29      (![X0 : $i, X1 : $i]:
% 1.10/1.29         (~ (r1_tarski @ (k3_tarski @ (k2_tarski @ X1 @ X0)) @ X1)
% 1.10/1.29          | ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (X1)))),
% 1.10/1.29      inference('sup-', [status(thm)], ['61', '62'])).
% 1.10/1.29  thf('64', plain,
% 1.10/1.29      (((k3_tarski @ (k2_tarski @ (k3_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A)))
% 1.10/1.29         = (k3_relat_1 @ sk_B))),
% 1.10/1.29      inference('sup-', [status(thm)], ['60', '63'])).
% 1.10/1.29  thf('65', plain, ((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 1.10/1.29      inference('demod', [status(thm)], ['37', '38', '64'])).
% 1.10/1.29  thf('66', plain, ($false), inference('demod', [status(thm)], ['0', '65'])).
% 1.10/1.29  
% 1.10/1.29  % SZS output end Refutation
% 1.10/1.29  
% 1.10/1.30  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
