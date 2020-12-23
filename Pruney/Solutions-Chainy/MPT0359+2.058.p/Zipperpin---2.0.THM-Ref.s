%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nzBoJrYkZ2

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 284 expanded)
%              Number of leaves         :   31 (  95 expanded)
%              Depth                    :   14
%              Number of atoms          :  718 (2229 expanded)
%              Number of equality atoms :   69 ( 206 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t39_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B )
      <=> ( B
          = ( k2_subset_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B )
        <=> ( B
            = ( k2_subset_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('1',plain,(
    ! [X57: $i,X58: $i] :
      ( ( ( k3_subset_1 @ X58 @ ( k3_subset_1 @ X58 @ X57 ) )
        = X57 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ X58 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X53: $i,X54: $i] :
      ( ( ( k3_subset_1 @ X53 @ X54 )
        = ( k4_xboole_0 @ X53 @ X54 ) )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['2','5'])).

thf(t38_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
      <=> ( B
          = ( k1_subset_1 @ A ) ) ) ) )).

thf('8',plain,(
    ! [X59: $i,X60: $i] :
      ( ~ ( r1_tarski @ X60 @ ( k3_subset_1 @ X59 @ X60 ) )
      | ( X60
        = ( k1_subset_1 @ X59 ) )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ X59 ) ) ) ),
    inference(cnf,[status(esa)],[t38_subset_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('9',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('10',plain,(
    ! [X59: $i,X60: $i] :
      ( ~ ( r1_tarski @ X60 @ ( k3_subset_1 @ X59 @ X60 ) )
      | ( X60
        = ( k1_subset_1 @ X59 ) )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ X59 ) ) ) ),
    inference(cnf,[status(esa)],[t38_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( k1_xboole_0
        = ( k1_subset_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t80_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('12',plain,(
    ! [X48: $i] :
      ( r1_tarski @ ( k1_tarski @ X48 ) @ ( k1_zfmisc_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t80_zfmisc_1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('13',plain,(
    ! [X14: $i] :
      ( ( k2_tarski @ X14 @ X14 )
      = ( k1_tarski @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( r2_hidden @ X44 @ X45 )
      | ~ ( r1_tarski @ ( k2_tarski @ X44 @ X46 ) @ X45 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('17',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( r2_hidden @ X49 @ X50 )
      | ( m1_subset_1 @ X49 @ X50 )
      | ( v1_xboole_0 @ X50 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('19',plain,(
    ! [X49: $i,X50: $i] :
      ( ( m1_subset_1 @ X49 @ X50 )
      | ~ ( r2_hidden @ X49 @ X50 ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('21',plain,(
    ! [X55: $i,X56: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X55 @ X56 ) @ ( k1_zfmisc_1 @ X55 ) )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('24',plain,(
    ! [X53: $i,X54: $i] :
      ( ( ( k3_subset_1 @ X53 @ X54 )
        = ( k4_xboole_0 @ X53 @ X54 ) )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('26',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('27',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('29',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k1_subset_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','32'])).

thf('34',plain,(
    ! [X59: $i,X60: $i] :
      ( ~ ( r1_tarski @ X60 @ ( k3_subset_1 @ X59 @ X60 ) )
      | ( X60 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ X59 ) ) ) ),
    inference(demod,[status(thm)],['8','33'])).

thf('35',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) @ sk_B_1 )
    | ~ ( m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','34'])).

thf('36',plain,
    ( ( sk_B_1
      = ( k2_subset_1 @ sk_A ) )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('39',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) @ sk_B_1 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_B_1
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( sk_B_1
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('43',plain,(
    ! [X52: $i] :
      ( ( k2_subset_1 @ X52 )
      = X52 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('44',plain,
    ( ( sk_B_1
      = ( k2_subset_1 @ sk_A ) )
   <= ( sk_B_1
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['36'])).

thf('45',plain,
    ( ( sk_B_1 = sk_A )
   <= ( sk_B_1
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ sk_A ) )
   <= ( sk_B_1
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X53: $i,X54: $i] :
      ( ( ( k3_subset_1 @ X53 @ X54 )
        = ( k4_xboole_0 @ X53 @ X54 ) )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('49',plain,
    ( ( ( k3_subset_1 @ sk_A @ sk_A )
      = ( k4_xboole_0 @ sk_A @ sk_A ) )
   <= ( sk_B_1
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_B_1 = sk_A )
   <= ( sk_B_1
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('51',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['40'])).

thf('52',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
      & ( sk_B_1
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( sk_B_1 = sk_A )
   <= ( sk_B_1
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('54',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_A ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
      & ( sk_B_1
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_A ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
      & ( sk_B_1
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
      & ( sk_B_1
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['42','55'])).

thf('57',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('58',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
    | ( sk_B_1
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
    | ( sk_B_1
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['36'])).

thf('60',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['41','58','59'])).

thf('61',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) @ sk_B_1 ),
    inference(simpl_trail,[status(thm)],['39','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X55: $i,X56: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X55 @ X56 ) @ ( k1_zfmisc_1 @ X55 ) )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('64',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('66',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['35','61','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('69',plain,(
    ! [X57: $i,X58: $i] :
      ( ( ( k3_subset_1 @ X58 @ ( k3_subset_1 @ X58 @ X57 ) )
        = X57 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ X58 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','30'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    sk_A = sk_B_1 ),
    inference(demod,[status(thm)],['6','67','72'])).

thf('74',plain,
    ( ( sk_B_1
     != ( k2_subset_1 @ sk_A ) )
   <= ( sk_B_1
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['40'])).

thf('75',plain,(
    ! [X52: $i] :
      ( ( k2_subset_1 @ X52 )
      = X52 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('76',plain,
    ( ( sk_B_1 != sk_A )
   <= ( sk_B_1
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    sk_B_1
 != ( k2_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['41','58'])).

thf('78',plain,(
    sk_B_1 != sk_A ),
    inference(simpl_trail,[status(thm)],['76','77'])).

thf('79',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['73','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nzBoJrYkZ2
% 0.15/0.34  % Computer   : n024.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 14:19:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 190 iterations in 0.043s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.21/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.21/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.50  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(t39_subset_1, conjecture,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.50       ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.21/0.50         ( ( B ) = ( k2_subset_1 @ A ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i]:
% 0.21/0.50        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.50          ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.21/0.50            ( ( B ) = ( k2_subset_1 @ A ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t39_subset_1])).
% 0.21/0.50  thf('0', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(involutiveness_k3_subset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.50       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (![X57 : $i, X58 : $i]:
% 0.21/0.50         (((k3_subset_1 @ X58 @ (k3_subset_1 @ X58 @ X57)) = (X57))
% 0.21/0.50          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ X58)))),
% 0.21/0.50      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.50  thf('3', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(d5_subset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.50       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X53 : $i, X54 : $i]:
% 0.21/0.50         (((k3_subset_1 @ X53 @ X54) = (k4_xboole_0 @ X53 @ X54))
% 0.21/0.50          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ X53)))),
% 0.21/0.50      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.21/0.50      inference('demod', [status(thm)], ['2', '5'])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.21/0.50      inference('demod', [status(thm)], ['2', '5'])).
% 0.21/0.50  thf(t38_subset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.50       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.21/0.50         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X59 : $i, X60 : $i]:
% 0.21/0.50         (~ (r1_tarski @ X60 @ (k3_subset_1 @ X59 @ X60))
% 0.21/0.50          | ((X60) = (k1_subset_1 @ X59))
% 0.21/0.50          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ X59)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t38_subset_1])).
% 0.21/0.50  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.50  thf('9', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.21/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (![X59 : $i, X60 : $i]:
% 0.21/0.50         (~ (r1_tarski @ X60 @ (k3_subset_1 @ X59 @ X60))
% 0.21/0.50          | ((X60) = (k1_subset_1 @ X59))
% 0.21/0.50          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ X59)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t38_subset_1])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.21/0.50          | ((k1_xboole_0) = (k1_subset_1 @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.50  thf(t80_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (![X48 : $i]: (r1_tarski @ (k1_tarski @ X48) @ (k1_zfmisc_1 @ X48))),
% 0.21/0.50      inference('cnf', [status(esa)], [t80_zfmisc_1])).
% 0.21/0.50  thf(t69_enumset1, axiom,
% 0.21/0.50    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (![X14 : $i]: ((k2_tarski @ X14 @ X14) = (k1_tarski @ X14))),
% 0.21/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.50  thf(t38_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.21/0.50       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.21/0.50         ((r2_hidden @ X44 @ X45)
% 0.21/0.50          | ~ (r1_tarski @ (k2_tarski @ X44 @ X46) @ X45))),
% 0.21/0.50      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.50  thf('16', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['12', '15'])).
% 0.21/0.50  thf(d2_subset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( v1_xboole_0 @ A ) =>
% 0.21/0.50         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.21/0.50       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.50         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (![X49 : $i, X50 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X49 @ X50)
% 0.21/0.50          | (m1_subset_1 @ X49 @ X50)
% 0.21/0.50          | (v1_xboole_0 @ X50))),
% 0.21/0.50      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.50  thf(d1_xboole_0, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (![X49 : $i, X50 : $i]:
% 0.21/0.50         ((m1_subset_1 @ X49 @ X50) | ~ (r2_hidden @ X49 @ X50))),
% 0.21/0.50      inference('clc', [status(thm)], ['17', '18'])).
% 0.21/0.50  thf('20', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['16', '19'])).
% 0.21/0.50  thf(dt_k3_subset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.50       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      (![X55 : $i, X56 : $i]:
% 0.21/0.50         ((m1_subset_1 @ (k3_subset_1 @ X55 @ X56) @ (k1_zfmisc_1 @ X55))
% 0.21/0.50          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ X55)))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (![X0 : $i]: (m1_subset_1 @ (k3_subset_1 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.50  thf('23', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['16', '19'])).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      (![X53 : $i, X54 : $i]:
% 0.21/0.50         (((k3_subset_1 @ X53 @ X54) = (k4_xboole_0 @ X53 @ X54))
% 0.21/0.50          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ X53)))),
% 0.21/0.50      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.50  thf(idempotence_k3_xboole_0, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.21/0.50  thf('26', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 0.21/0.50      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.21/0.50  thf(t100_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      (![X5 : $i, X6 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ X5 @ X6)
% 0.21/0.50           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['26', '27'])).
% 0.21/0.50  thf(t92_xboole_1, axiom,
% 0.21/0.50    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.50  thf('29', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ X11) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.21/0.50  thf('30', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['28', '29'])).
% 0.21/0.50  thf('31', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['25', '30'])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['22', '31'])).
% 0.21/0.50  thf('33', plain, (![X0 : $i]: ((k1_xboole_0) = (k1_subset_1 @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['11', '32'])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      (![X59 : $i, X60 : $i]:
% 0.21/0.50         (~ (r1_tarski @ X60 @ (k3_subset_1 @ X59 @ X60))
% 0.21/0.50          | ((X60) = (k1_xboole_0))
% 0.21/0.50          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ X59)))),
% 0.21/0.50      inference('demod', [status(thm)], ['8', '33'])).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      ((~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B_1) @ sk_B_1)
% 0.21/0.50        | ~ (m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.50        | ((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['7', '34'])).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      ((((sk_B_1) = (k2_subset_1 @ sk_A))
% 0.21/0.50        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1))
% 0.21/0.50         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1)))),
% 0.21/0.50      inference('split', [status(esa)], ['36'])).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.50  thf('39', plain,
% 0.21/0.50      (((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B_1) @ sk_B_1))
% 0.21/0.50         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1)))),
% 0.21/0.50      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.50  thf('40', plain,
% 0.21/0.50      ((((sk_B_1) != (k2_subset_1 @ sk_A))
% 0.21/0.50        | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('41', plain,
% 0.21/0.50      (~ (((sk_B_1) = (k2_subset_1 @ sk_A))) | 
% 0.21/0.50       ~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 0.21/0.50      inference('split', [status(esa)], ['40'])).
% 0.21/0.50  thf('42', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['28', '29'])).
% 0.21/0.50  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.21/0.50  thf('43', plain, (![X52 : $i]: ((k2_subset_1 @ X52) = (X52))),
% 0.21/0.50      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.50  thf('44', plain,
% 0.21/0.50      ((((sk_B_1) = (k2_subset_1 @ sk_A)))
% 0.21/0.50         <= ((((sk_B_1) = (k2_subset_1 @ sk_A))))),
% 0.21/0.50      inference('split', [status(esa)], ['36'])).
% 0.21/0.50  thf('45', plain,
% 0.21/0.50      ((((sk_B_1) = (sk_A))) <= ((((sk_B_1) = (k2_subset_1 @ sk_A))))),
% 0.21/0.50      inference('sup+', [status(thm)], ['43', '44'])).
% 0.21/0.50  thf('46', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('47', plain,
% 0.21/0.50      (((m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ sk_A)))
% 0.21/0.50         <= ((((sk_B_1) = (k2_subset_1 @ sk_A))))),
% 0.21/0.50      inference('sup+', [status(thm)], ['45', '46'])).
% 0.21/0.50  thf('48', plain,
% 0.21/0.50      (![X53 : $i, X54 : $i]:
% 0.21/0.50         (((k3_subset_1 @ X53 @ X54) = (k4_xboole_0 @ X53 @ X54))
% 0.21/0.50          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ X53)))),
% 0.21/0.50      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.50  thf('49', plain,
% 0.21/0.50      ((((k3_subset_1 @ sk_A @ sk_A) = (k4_xboole_0 @ sk_A @ sk_A)))
% 0.21/0.50         <= ((((sk_B_1) = (k2_subset_1 @ sk_A))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.50  thf('50', plain,
% 0.21/0.50      ((((sk_B_1) = (sk_A))) <= ((((sk_B_1) = (k2_subset_1 @ sk_A))))),
% 0.21/0.50      inference('sup+', [status(thm)], ['43', '44'])).
% 0.21/0.50  thf('51', plain,
% 0.21/0.50      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1))
% 0.21/0.50         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1)))),
% 0.21/0.50      inference('split', [status(esa)], ['40'])).
% 0.21/0.50  thf('52', plain,
% 0.21/0.50      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_A))
% 0.21/0.50         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1)) & 
% 0.21/0.50             (((sk_B_1) = (k2_subset_1 @ sk_A))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.50  thf('53', plain,
% 0.21/0.50      ((((sk_B_1) = (sk_A))) <= ((((sk_B_1) = (k2_subset_1 @ sk_A))))),
% 0.21/0.50      inference('sup+', [status(thm)], ['43', '44'])).
% 0.21/0.50  thf('54', plain,
% 0.21/0.50      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_A) @ sk_A))
% 0.21/0.50         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1)) & 
% 0.21/0.50             (((sk_B_1) = (k2_subset_1 @ sk_A))))),
% 0.21/0.50      inference('demod', [status(thm)], ['52', '53'])).
% 0.21/0.50  thf('55', plain,
% 0.21/0.50      ((~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_A) @ sk_A))
% 0.21/0.50         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1)) & 
% 0.21/0.50             (((sk_B_1) = (k2_subset_1 @ sk_A))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['49', '54'])).
% 0.21/0.50  thf('56', plain,
% 0.21/0.50      ((~ (r1_tarski @ k1_xboole_0 @ sk_A))
% 0.21/0.50         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1)) & 
% 0.21/0.50             (((sk_B_1) = (k2_subset_1 @ sk_A))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['42', '55'])).
% 0.21/0.50  thf('57', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.21/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.50  thf('58', plain,
% 0.21/0.50      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1)) | 
% 0.21/0.50       ~ (((sk_B_1) = (k2_subset_1 @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['56', '57'])).
% 0.21/0.50  thf('59', plain,
% 0.21/0.50      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1)) | 
% 0.21/0.50       (((sk_B_1) = (k2_subset_1 @ sk_A)))),
% 0.21/0.50      inference('split', [status(esa)], ['36'])).
% 0.21/0.50  thf('60', plain, (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 0.21/0.50      inference('sat_resolution*', [status(thm)], ['41', '58', '59'])).
% 0.21/0.50  thf('61', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B_1) @ sk_B_1)),
% 0.21/0.50      inference('simpl_trail', [status(thm)], ['39', '60'])).
% 0.21/0.50  thf('62', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('63', plain,
% 0.21/0.50      (![X55 : $i, X56 : $i]:
% 0.21/0.50         ((m1_subset_1 @ (k3_subset_1 @ X55 @ X56) @ (k1_zfmisc_1 @ X55))
% 0.21/0.50          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ X55)))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.21/0.50  thf('64', plain,
% 0.21/0.50      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['62', '63'])).
% 0.21/0.50  thf('65', plain,
% 0.21/0.50      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.50  thf('66', plain,
% 0.21/0.50      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['64', '65'])).
% 0.21/0.50  thf('67', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['35', '61', '66'])).
% 0.21/0.50  thf('68', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['16', '19'])).
% 0.21/0.50  thf('69', plain,
% 0.21/0.50      (![X57 : $i, X58 : $i]:
% 0.21/0.50         (((k3_subset_1 @ X58 @ (k3_subset_1 @ X58 @ X57)) = (X57))
% 0.21/0.50          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ X58)))),
% 0.21/0.50      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.21/0.50  thf('70', plain,
% 0.21/0.50      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['68', '69'])).
% 0.21/0.50  thf('71', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['25', '30'])).
% 0.21/0.50  thf('72', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['70', '71'])).
% 0.21/0.50  thf('73', plain, (((sk_A) = (sk_B_1))),
% 0.21/0.50      inference('demod', [status(thm)], ['6', '67', '72'])).
% 0.21/0.50  thf('74', plain,
% 0.21/0.50      ((((sk_B_1) != (k2_subset_1 @ sk_A)))
% 0.21/0.50         <= (~ (((sk_B_1) = (k2_subset_1 @ sk_A))))),
% 0.21/0.50      inference('split', [status(esa)], ['40'])).
% 0.21/0.50  thf('75', plain, (![X52 : $i]: ((k2_subset_1 @ X52) = (X52))),
% 0.21/0.50      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.50  thf('76', plain,
% 0.21/0.50      ((((sk_B_1) != (sk_A))) <= (~ (((sk_B_1) = (k2_subset_1 @ sk_A))))),
% 0.21/0.50      inference('demod', [status(thm)], ['74', '75'])).
% 0.21/0.50  thf('77', plain, (~ (((sk_B_1) = (k2_subset_1 @ sk_A)))),
% 0.21/0.50      inference('sat_resolution*', [status(thm)], ['41', '58'])).
% 0.21/0.50  thf('78', plain, (((sk_B_1) != (sk_A))),
% 0.21/0.50      inference('simpl_trail', [status(thm)], ['76', '77'])).
% 0.21/0.50  thf('79', plain, ($false),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['73', '78'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
