%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JTm95KZSEe

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:06 EST 2020

% Result     : Theorem 1.10s
% Output     : Refutation 1.10s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 331 expanded)
%              Number of leaves         :   27 ( 112 expanded)
%              Depth                    :   15
%              Number of atoms          :  607 (2274 expanded)
%              Number of equality atoms :   55 ( 209 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t28_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) )
          = ( k2_subset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_subset_1])).

thf('0',plain,(
    ( k4_subset_1 @ sk_A @ sk_B_1 @ ( k2_subset_1 @ sk_A ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('1',plain,(
    ! [X54: $i] :
      ( ( k2_subset_1 @ X54 )
      = X54 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('2',plain,(
    ! [X54: $i] :
      ( ( k2_subset_1 @ X54 )
      = X54 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('3',plain,(
    ( k4_subset_1 @ sk_A @ sk_B_1 @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X55: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X55 ) @ ( k1_zfmisc_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf('5',plain,(
    ! [X54: $i] :
      ( ( k2_subset_1 @ X54 )
      = X54 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('6',plain,(
    ! [X55: $i] :
      ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ X55 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ X64 ) )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ X64 ) )
      | ( ( k4_subset_1 @ X64 @ X63 @ X65 )
        = ( k2_xboole_0 @ X63 @ X65 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B_1 @ X0 )
        = ( k2_xboole_0 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ( k2_xboole_0 @ sk_B_1 @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['3','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('13',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X51 @ X52 )
      | ( r2_hidden @ X51 @ X52 )
      | ( v1_xboole_0 @ X52 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('14',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('15',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( r2_hidden @ X42 @ X41 )
      | ( r1_tarski @ X42 @ X40 )
      | ( X41
       != ( k1_zfmisc_1 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('16',plain,(
    ! [X40: $i,X42: $i] :
      ( ( r1_tarski @ X42 @ X40 )
      | ~ ( r2_hidden @ X42 @ ( k1_zfmisc_1 @ X40 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r1_tarski @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
      = sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X55: $i] :
      ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ X55 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('21',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X53 @ X52 )
      | ( v1_xboole_0 @ X53 )
      | ~ ( v1_xboole_0 @ X52 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
      = sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ( k2_xboole_0 @ sk_B_1 @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['3','10'])).

thf('25',plain,
    ( ( sk_A != sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['25'])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('27',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('28',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('29',plain,(
    ! [X5: $i] :
      ( ( X5 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    sk_A = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    sk_A = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['26','29'])).

thf('32',plain,(
    ( k2_xboole_0 @ sk_B_1 @ o_0_0_xboole_0 )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['11','30','31'])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
      = sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('34',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X53 @ X52 )
      | ( v1_xboole_0 @ X53 )
      | ~ ( v1_xboole_0 @ X52 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('36',plain,
    ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
      = sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ( k2_xboole_0 @ sk_B_1 @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['3','10'])).

thf('39',plain,
    ( ( sk_A != sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X5: $i] :
      ( ( X5 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('42',plain,(
    sk_B_1 = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ( k2_xboole_0 @ o_0_0_xboole_0 @ o_0_0_xboole_0 )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['32','42'])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
      = sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('45',plain,(
    ! [X5: $i] :
      ( ( X5 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('46',plain,
    ( ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
      = sk_A )
    | ( ( k1_zfmisc_1 @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ( k2_xboole_0 @ sk_B_1 @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['3','10'])).

thf('48',plain,
    ( ( sk_A != sk_A )
    | ( ( k1_zfmisc_1 @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k1_zfmisc_1 @ sk_A )
    = o_0_0_xboole_0 ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    sk_A = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['26','29'])).

thf('51',plain,
    ( ( k1_zfmisc_1 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X55: $i] :
      ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ X55 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('53',plain,(
    ! [X55: $i] :
      ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ X55 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                 => ( r2_hidden @ D @ C ) ) )
           => ( r1_tarski @ B @ C ) ) ) ) )).

thf('54',plain,(
    ! [X70: $i,X71: $i,X72: $i] :
      ( ~ ( m1_subset_1 @ X70 @ ( k1_zfmisc_1 @ X71 ) )
      | ( r1_tarski @ X72 @ X70 )
      | ( r2_hidden @ ( sk_D @ X70 @ X72 @ X71 ) @ X72 )
      | ~ ( m1_subset_1 @ X72 @ ( k1_zfmisc_1 @ X71 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X55: $i] :
      ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ X55 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('58',plain,(
    ! [X55: $i] :
      ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ X55 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('59',plain,(
    ! [X70: $i,X71: $i,X72: $i] :
      ( ~ ( m1_subset_1 @ X70 @ ( k1_zfmisc_1 @ X71 ) )
      | ( r1_tarski @ X72 @ X70 )
      | ~ ( r2_hidden @ ( sk_D @ X70 @ X72 @ X71 ) @ X70 )
      | ~ ( m1_subset_1 @ X72 @ ( k1_zfmisc_1 @ X71 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(clc,[status(thm)],['56','61'])).

thf('63',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( r1_tarski @ X39 @ X40 )
      | ( r2_hidden @ X39 @ X41 )
      | ( X41
       != ( k1_zfmisc_1 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('64',plain,(
    ! [X39: $i,X40: $i] :
      ( ( r2_hidden @ X39 @ ( k1_zfmisc_1 @ X40 ) )
      | ~ ( r1_tarski @ X39 @ X40 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','64'])).

thf('66',plain,(
    r2_hidden @ o_0_0_xboole_0 @ o_0_0_xboole_0 ),
    inference('sup+',[status(thm)],['51','65'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('67',plain,(
    ! [X69: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X69 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('68',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('69',plain,(
    ! [X69: $i] :
      ( m1_subset_1 @ o_0_0_xboole_0 @ ( k1_zfmisc_1 @ X69 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('70',plain,(
    ! [X60: $i,X61: $i,X62: $i] :
      ( ~ ( r2_hidden @ X60 @ X61 )
      | ( r2_hidden @ X60 @ X62 )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ X62 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( r2_hidden @ o_0_0_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['66','71'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('73',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X8 )
      | ( X9 = X6 )
      | ( X8
       != ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('74',plain,(
    ! [X6: $i,X9: $i] :
      ( ( X9 = X6 )
      | ~ ( r2_hidden @ X9 @ ( k1_tarski @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i] : ( o_0_0_xboole_0 = X0 ) ),
    inference('sup-',[status(thm)],['72','74'])).

thf('76',plain,(
    o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['43','75'])).

thf('77',plain,(
    $false ),
    inference(simplify,[status(thm)],['76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JTm95KZSEe
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:59:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.10/1.29  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.10/1.29  % Solved by: fo/fo7.sh
% 1.10/1.29  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.10/1.29  % done 2055 iterations in 0.879s
% 1.10/1.29  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.10/1.29  % SZS output start Refutation
% 1.10/1.29  thf(sk_A_type, type, sk_A: $i).
% 1.10/1.29  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.10/1.29  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.10/1.29  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 1.10/1.29  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.10/1.29  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.10/1.29  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.10/1.29  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.10/1.29  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.10/1.29  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.10/1.29  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.10/1.29  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.10/1.29  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.10/1.29  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.10/1.29  thf(t28_subset_1, conjecture,
% 1.10/1.30    (![A:$i,B:$i]:
% 1.10/1.30     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.10/1.30       ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ))).
% 1.10/1.30  thf(zf_stmt_0, negated_conjecture,
% 1.10/1.30    (~( ![A:$i,B:$i]:
% 1.10/1.30        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.10/1.30          ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ) )),
% 1.10/1.30    inference('cnf.neg', [status(esa)], [t28_subset_1])).
% 1.10/1.30  thf('0', plain,
% 1.10/1.30      (((k4_subset_1 @ sk_A @ sk_B_1 @ (k2_subset_1 @ sk_A))
% 1.10/1.30         != (k2_subset_1 @ sk_A))),
% 1.10/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.30  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.10/1.30  thf('1', plain, (![X54 : $i]: ((k2_subset_1 @ X54) = (X54))),
% 1.10/1.30      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.10/1.30  thf('2', plain, (![X54 : $i]: ((k2_subset_1 @ X54) = (X54))),
% 1.10/1.30      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.10/1.30  thf('3', plain, (((k4_subset_1 @ sk_A @ sk_B_1 @ sk_A) != (sk_A))),
% 1.10/1.30      inference('demod', [status(thm)], ['0', '1', '2'])).
% 1.10/1.30  thf(dt_k2_subset_1, axiom,
% 1.10/1.30    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.10/1.30  thf('4', plain,
% 1.10/1.30      (![X55 : $i]: (m1_subset_1 @ (k2_subset_1 @ X55) @ (k1_zfmisc_1 @ X55))),
% 1.10/1.30      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 1.10/1.30  thf('5', plain, (![X54 : $i]: ((k2_subset_1 @ X54) = (X54))),
% 1.10/1.30      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.10/1.30  thf('6', plain, (![X55 : $i]: (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ X55))),
% 1.10/1.30      inference('demod', [status(thm)], ['4', '5'])).
% 1.10/1.30  thf('7', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 1.10/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.30  thf(redefinition_k4_subset_1, axiom,
% 1.10/1.30    (![A:$i,B:$i,C:$i]:
% 1.10/1.30     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.10/1.30         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.10/1.30       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.10/1.30  thf('8', plain,
% 1.10/1.30      (![X63 : $i, X64 : $i, X65 : $i]:
% 1.10/1.30         (~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ X64))
% 1.10/1.30          | ~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ X64))
% 1.10/1.30          | ((k4_subset_1 @ X64 @ X63 @ X65) = (k2_xboole_0 @ X63 @ X65)))),
% 1.10/1.30      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.10/1.30  thf('9', plain,
% 1.10/1.30      (![X0 : $i]:
% 1.10/1.30         (((k4_subset_1 @ sk_A @ sk_B_1 @ X0) = (k2_xboole_0 @ sk_B_1 @ X0))
% 1.10/1.30          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 1.10/1.30      inference('sup-', [status(thm)], ['7', '8'])).
% 1.10/1.30  thf('10', plain,
% 1.10/1.30      (((k4_subset_1 @ sk_A @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_A))),
% 1.10/1.30      inference('sup-', [status(thm)], ['6', '9'])).
% 1.10/1.30  thf('11', plain, (((k2_xboole_0 @ sk_B_1 @ sk_A) != (sk_A))),
% 1.10/1.30      inference('demod', [status(thm)], ['3', '10'])).
% 1.10/1.30  thf('12', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 1.10/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.30  thf(d2_subset_1, axiom,
% 1.10/1.30    (![A:$i,B:$i]:
% 1.10/1.30     ( ( ( v1_xboole_0 @ A ) =>
% 1.10/1.30         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.10/1.30       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.10/1.30         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.10/1.30  thf('13', plain,
% 1.10/1.30      (![X51 : $i, X52 : $i]:
% 1.10/1.30         (~ (m1_subset_1 @ X51 @ X52)
% 1.10/1.30          | (r2_hidden @ X51 @ X52)
% 1.10/1.30          | (v1_xboole_0 @ X52))),
% 1.10/1.30      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.10/1.30  thf('14', plain,
% 1.10/1.30      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 1.10/1.30        | (r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A)))),
% 1.10/1.30      inference('sup-', [status(thm)], ['12', '13'])).
% 1.10/1.30  thf(d1_zfmisc_1, axiom,
% 1.10/1.30    (![A:$i,B:$i]:
% 1.10/1.30     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 1.10/1.30       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 1.10/1.30  thf('15', plain,
% 1.10/1.30      (![X40 : $i, X41 : $i, X42 : $i]:
% 1.10/1.30         (~ (r2_hidden @ X42 @ X41)
% 1.10/1.30          | (r1_tarski @ X42 @ X40)
% 1.10/1.30          | ((X41) != (k1_zfmisc_1 @ X40)))),
% 1.10/1.30      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.10/1.30  thf('16', plain,
% 1.10/1.30      (![X40 : $i, X42 : $i]:
% 1.10/1.30         ((r1_tarski @ X42 @ X40) | ~ (r2_hidden @ X42 @ (k1_zfmisc_1 @ X40)))),
% 1.10/1.30      inference('simplify', [status(thm)], ['15'])).
% 1.10/1.30  thf('17', plain,
% 1.10/1.30      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A)) | (r1_tarski @ sk_B_1 @ sk_A))),
% 1.10/1.30      inference('sup-', [status(thm)], ['14', '16'])).
% 1.10/1.30  thf(t12_xboole_1, axiom,
% 1.10/1.30    (![A:$i,B:$i]:
% 1.10/1.30     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.10/1.30  thf('18', plain,
% 1.10/1.30      (![X2 : $i, X3 : $i]:
% 1.10/1.30         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 1.10/1.30      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.10/1.30  thf('19', plain,
% 1.10/1.30      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 1.10/1.30        | ((k2_xboole_0 @ sk_B_1 @ sk_A) = (sk_A)))),
% 1.10/1.30      inference('sup-', [status(thm)], ['17', '18'])).
% 1.10/1.30  thf('20', plain, (![X55 : $i]: (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ X55))),
% 1.10/1.30      inference('demod', [status(thm)], ['4', '5'])).
% 1.10/1.30  thf('21', plain,
% 1.10/1.30      (![X52 : $i, X53 : $i]:
% 1.10/1.30         (~ (m1_subset_1 @ X53 @ X52)
% 1.10/1.30          | (v1_xboole_0 @ X53)
% 1.10/1.30          | ~ (v1_xboole_0 @ X52))),
% 1.10/1.30      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.10/1.30  thf('22', plain,
% 1.10/1.30      (![X0 : $i]: (~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0)) | (v1_xboole_0 @ X0))),
% 1.10/1.30      inference('sup-', [status(thm)], ['20', '21'])).
% 1.10/1.30  thf('23', plain,
% 1.10/1.30      ((((k2_xboole_0 @ sk_B_1 @ sk_A) = (sk_A)) | (v1_xboole_0 @ sk_A))),
% 1.10/1.30      inference('sup-', [status(thm)], ['19', '22'])).
% 1.10/1.30  thf('24', plain, (((k2_xboole_0 @ sk_B_1 @ sk_A) != (sk_A))),
% 1.10/1.30      inference('demod', [status(thm)], ['3', '10'])).
% 1.10/1.30  thf('25', plain, ((((sk_A) != (sk_A)) | (v1_xboole_0 @ sk_A))),
% 1.10/1.30      inference('sup-', [status(thm)], ['23', '24'])).
% 1.10/1.30  thf('26', plain, ((v1_xboole_0 @ sk_A)),
% 1.10/1.30      inference('simplify', [status(thm)], ['25'])).
% 1.10/1.30  thf(t6_boole, axiom,
% 1.10/1.30    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.10/1.30  thf('27', plain,
% 1.10/1.30      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X5))),
% 1.10/1.30      inference('cnf', [status(esa)], [t6_boole])).
% 1.10/1.30  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 1.10/1.30  thf('28', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 1.10/1.30      inference('cnf', [status(esa)], [d2_xboole_0])).
% 1.10/1.30  thf('29', plain,
% 1.10/1.30      (![X5 : $i]: (((X5) = (o_0_0_xboole_0)) | ~ (v1_xboole_0 @ X5))),
% 1.10/1.30      inference('demod', [status(thm)], ['27', '28'])).
% 1.10/1.30  thf('30', plain, (((sk_A) = (o_0_0_xboole_0))),
% 1.10/1.30      inference('sup-', [status(thm)], ['26', '29'])).
% 1.10/1.30  thf('31', plain, (((sk_A) = (o_0_0_xboole_0))),
% 1.10/1.30      inference('sup-', [status(thm)], ['26', '29'])).
% 1.10/1.30  thf('32', plain,
% 1.10/1.30      (((k2_xboole_0 @ sk_B_1 @ o_0_0_xboole_0) != (o_0_0_xboole_0))),
% 1.10/1.30      inference('demod', [status(thm)], ['11', '30', '31'])).
% 1.10/1.30  thf('33', plain,
% 1.10/1.30      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 1.10/1.30        | ((k2_xboole_0 @ sk_B_1 @ sk_A) = (sk_A)))),
% 1.10/1.30      inference('sup-', [status(thm)], ['17', '18'])).
% 1.10/1.30  thf('34', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 1.10/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.30  thf('35', plain,
% 1.10/1.30      (![X52 : $i, X53 : $i]:
% 1.10/1.30         (~ (m1_subset_1 @ X53 @ X52)
% 1.10/1.30          | (v1_xboole_0 @ X53)
% 1.10/1.30          | ~ (v1_xboole_0 @ X52))),
% 1.10/1.30      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.10/1.30  thf('36', plain,
% 1.10/1.30      ((~ (v1_xboole_0 @ (k1_zfmisc_1 @ sk_A)) | (v1_xboole_0 @ sk_B_1))),
% 1.10/1.30      inference('sup-', [status(thm)], ['34', '35'])).
% 1.10/1.30  thf('37', plain,
% 1.10/1.30      ((((k2_xboole_0 @ sk_B_1 @ sk_A) = (sk_A)) | (v1_xboole_0 @ sk_B_1))),
% 1.10/1.30      inference('sup-', [status(thm)], ['33', '36'])).
% 1.10/1.30  thf('38', plain, (((k2_xboole_0 @ sk_B_1 @ sk_A) != (sk_A))),
% 1.10/1.30      inference('demod', [status(thm)], ['3', '10'])).
% 1.10/1.30  thf('39', plain, ((((sk_A) != (sk_A)) | (v1_xboole_0 @ sk_B_1))),
% 1.10/1.30      inference('sup-', [status(thm)], ['37', '38'])).
% 1.10/1.30  thf('40', plain, ((v1_xboole_0 @ sk_B_1)),
% 1.10/1.30      inference('simplify', [status(thm)], ['39'])).
% 1.10/1.30  thf('41', plain,
% 1.10/1.30      (![X5 : $i]: (((X5) = (o_0_0_xboole_0)) | ~ (v1_xboole_0 @ X5))),
% 1.10/1.30      inference('demod', [status(thm)], ['27', '28'])).
% 1.10/1.30  thf('42', plain, (((sk_B_1) = (o_0_0_xboole_0))),
% 1.10/1.30      inference('sup-', [status(thm)], ['40', '41'])).
% 1.10/1.30  thf('43', plain,
% 1.10/1.30      (((k2_xboole_0 @ o_0_0_xboole_0 @ o_0_0_xboole_0) != (o_0_0_xboole_0))),
% 1.10/1.30      inference('demod', [status(thm)], ['32', '42'])).
% 1.10/1.30  thf('44', plain,
% 1.10/1.30      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 1.10/1.30        | ((k2_xboole_0 @ sk_B_1 @ sk_A) = (sk_A)))),
% 1.10/1.30      inference('sup-', [status(thm)], ['17', '18'])).
% 1.10/1.30  thf('45', plain,
% 1.10/1.30      (![X5 : $i]: (((X5) = (o_0_0_xboole_0)) | ~ (v1_xboole_0 @ X5))),
% 1.10/1.30      inference('demod', [status(thm)], ['27', '28'])).
% 1.10/1.30  thf('46', plain,
% 1.10/1.30      ((((k2_xboole_0 @ sk_B_1 @ sk_A) = (sk_A))
% 1.10/1.30        | ((k1_zfmisc_1 @ sk_A) = (o_0_0_xboole_0)))),
% 1.10/1.30      inference('sup-', [status(thm)], ['44', '45'])).
% 1.10/1.30  thf('47', plain, (((k2_xboole_0 @ sk_B_1 @ sk_A) != (sk_A))),
% 1.10/1.30      inference('demod', [status(thm)], ['3', '10'])).
% 1.10/1.30  thf('48', plain,
% 1.10/1.30      ((((sk_A) != (sk_A)) | ((k1_zfmisc_1 @ sk_A) = (o_0_0_xboole_0)))),
% 1.10/1.30      inference('sup-', [status(thm)], ['46', '47'])).
% 1.10/1.30  thf('49', plain, (((k1_zfmisc_1 @ sk_A) = (o_0_0_xboole_0))),
% 1.10/1.30      inference('simplify', [status(thm)], ['48'])).
% 1.10/1.30  thf('50', plain, (((sk_A) = (o_0_0_xboole_0))),
% 1.10/1.30      inference('sup-', [status(thm)], ['26', '29'])).
% 1.10/1.30  thf('51', plain, (((k1_zfmisc_1 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 1.10/1.30      inference('demod', [status(thm)], ['49', '50'])).
% 1.10/1.30  thf('52', plain, (![X55 : $i]: (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ X55))),
% 1.10/1.30      inference('demod', [status(thm)], ['4', '5'])).
% 1.10/1.30  thf('53', plain, (![X55 : $i]: (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ X55))),
% 1.10/1.30      inference('demod', [status(thm)], ['4', '5'])).
% 1.10/1.30  thf(t7_subset_1, axiom,
% 1.10/1.30    (![A:$i,B:$i]:
% 1.10/1.30     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.10/1.30       ( ![C:$i]:
% 1.10/1.30         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.10/1.30           ( ( ![D:$i]:
% 1.10/1.30               ( ( m1_subset_1 @ D @ A ) =>
% 1.10/1.30                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 1.10/1.30             ( r1_tarski @ B @ C ) ) ) ) ))).
% 1.10/1.30  thf('54', plain,
% 1.10/1.30      (![X70 : $i, X71 : $i, X72 : $i]:
% 1.10/1.30         (~ (m1_subset_1 @ X70 @ (k1_zfmisc_1 @ X71))
% 1.10/1.30          | (r1_tarski @ X72 @ X70)
% 1.10/1.30          | (r2_hidden @ (sk_D @ X70 @ X72 @ X71) @ X72)
% 1.10/1.30          | ~ (m1_subset_1 @ X72 @ (k1_zfmisc_1 @ X71)))),
% 1.10/1.30      inference('cnf', [status(esa)], [t7_subset_1])).
% 1.10/1.30  thf('55', plain,
% 1.10/1.30      (![X0 : $i, X1 : $i]:
% 1.10/1.30         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 1.10/1.30          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 1.10/1.30          | (r1_tarski @ X1 @ X0))),
% 1.10/1.30      inference('sup-', [status(thm)], ['53', '54'])).
% 1.10/1.30  thf('56', plain,
% 1.10/1.30      (![X0 : $i]:
% 1.10/1.30         ((r1_tarski @ X0 @ X0) | (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0))),
% 1.10/1.30      inference('sup-', [status(thm)], ['52', '55'])).
% 1.10/1.30  thf('57', plain, (![X55 : $i]: (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ X55))),
% 1.10/1.30      inference('demod', [status(thm)], ['4', '5'])).
% 1.10/1.30  thf('58', plain, (![X55 : $i]: (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ X55))),
% 1.10/1.30      inference('demod', [status(thm)], ['4', '5'])).
% 1.10/1.30  thf('59', plain,
% 1.10/1.30      (![X70 : $i, X71 : $i, X72 : $i]:
% 1.10/1.30         (~ (m1_subset_1 @ X70 @ (k1_zfmisc_1 @ X71))
% 1.10/1.30          | (r1_tarski @ X72 @ X70)
% 1.10/1.30          | ~ (r2_hidden @ (sk_D @ X70 @ X72 @ X71) @ X70)
% 1.10/1.30          | ~ (m1_subset_1 @ X72 @ (k1_zfmisc_1 @ X71)))),
% 1.10/1.30      inference('cnf', [status(esa)], [t7_subset_1])).
% 1.10/1.30  thf('60', plain,
% 1.10/1.30      (![X0 : $i, X1 : $i]:
% 1.10/1.30         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 1.10/1.30          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.10/1.30          | (r1_tarski @ X1 @ X0))),
% 1.10/1.30      inference('sup-', [status(thm)], ['58', '59'])).
% 1.10/1.30  thf('61', plain,
% 1.10/1.30      (![X0 : $i]:
% 1.10/1.30         ((r1_tarski @ X0 @ X0) | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0))),
% 1.10/1.30      inference('sup-', [status(thm)], ['57', '60'])).
% 1.10/1.30  thf('62', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.10/1.30      inference('clc', [status(thm)], ['56', '61'])).
% 1.10/1.30  thf('63', plain,
% 1.10/1.30      (![X39 : $i, X40 : $i, X41 : $i]:
% 1.10/1.30         (~ (r1_tarski @ X39 @ X40)
% 1.10/1.30          | (r2_hidden @ X39 @ X41)
% 1.10/1.30          | ((X41) != (k1_zfmisc_1 @ X40)))),
% 1.10/1.30      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.10/1.30  thf('64', plain,
% 1.10/1.30      (![X39 : $i, X40 : $i]:
% 1.10/1.30         ((r2_hidden @ X39 @ (k1_zfmisc_1 @ X40)) | ~ (r1_tarski @ X39 @ X40))),
% 1.10/1.30      inference('simplify', [status(thm)], ['63'])).
% 1.10/1.30  thf('65', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.10/1.30      inference('sup-', [status(thm)], ['62', '64'])).
% 1.10/1.30  thf('66', plain, ((r2_hidden @ o_0_0_xboole_0 @ o_0_0_xboole_0)),
% 1.10/1.30      inference('sup+', [status(thm)], ['51', '65'])).
% 1.10/1.30  thf(t4_subset_1, axiom,
% 1.10/1.30    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.10/1.30  thf('67', plain,
% 1.10/1.30      (![X69 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X69))),
% 1.10/1.30      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.10/1.30  thf('68', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 1.10/1.30      inference('cnf', [status(esa)], [d2_xboole_0])).
% 1.10/1.30  thf('69', plain,
% 1.10/1.30      (![X69 : $i]: (m1_subset_1 @ o_0_0_xboole_0 @ (k1_zfmisc_1 @ X69))),
% 1.10/1.30      inference('demod', [status(thm)], ['67', '68'])).
% 1.10/1.30  thf(l3_subset_1, axiom,
% 1.10/1.30    (![A:$i,B:$i]:
% 1.10/1.30     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.10/1.30       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 1.10/1.30  thf('70', plain,
% 1.10/1.30      (![X60 : $i, X61 : $i, X62 : $i]:
% 1.10/1.30         (~ (r2_hidden @ X60 @ X61)
% 1.10/1.30          | (r2_hidden @ X60 @ X62)
% 1.10/1.30          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ X62)))),
% 1.10/1.30      inference('cnf', [status(esa)], [l3_subset_1])).
% 1.10/1.30  thf('71', plain,
% 1.10/1.30      (![X0 : $i, X1 : $i]:
% 1.10/1.30         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ o_0_0_xboole_0))),
% 1.10/1.30      inference('sup-', [status(thm)], ['69', '70'])).
% 1.10/1.30  thf('72', plain, (![X0 : $i]: (r2_hidden @ o_0_0_xboole_0 @ X0)),
% 1.10/1.30      inference('sup-', [status(thm)], ['66', '71'])).
% 1.10/1.30  thf(d1_tarski, axiom,
% 1.10/1.30    (![A:$i,B:$i]:
% 1.10/1.30     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.10/1.30       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.10/1.30  thf('73', plain,
% 1.10/1.30      (![X6 : $i, X8 : $i, X9 : $i]:
% 1.10/1.30         (~ (r2_hidden @ X9 @ X8) | ((X9) = (X6)) | ((X8) != (k1_tarski @ X6)))),
% 1.10/1.30      inference('cnf', [status(esa)], [d1_tarski])).
% 1.10/1.30  thf('74', plain,
% 1.10/1.30      (![X6 : $i, X9 : $i]:
% 1.10/1.30         (((X9) = (X6)) | ~ (r2_hidden @ X9 @ (k1_tarski @ X6)))),
% 1.10/1.30      inference('simplify', [status(thm)], ['73'])).
% 1.10/1.30  thf('75', plain, (![X0 : $i]: ((o_0_0_xboole_0) = (X0))),
% 1.10/1.30      inference('sup-', [status(thm)], ['72', '74'])).
% 1.10/1.30  thf('76', plain, (((o_0_0_xboole_0) != (o_0_0_xboole_0))),
% 1.10/1.30      inference('demod', [status(thm)], ['43', '75'])).
% 1.10/1.30  thf('77', plain, ($false), inference('simplify', [status(thm)], ['76'])).
% 1.10/1.30  
% 1.10/1.30  % SZS output end Refutation
% 1.10/1.30  
% 1.10/1.30  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
