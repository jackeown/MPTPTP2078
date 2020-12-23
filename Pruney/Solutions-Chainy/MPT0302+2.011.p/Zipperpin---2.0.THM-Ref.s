%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZTTJ2iLmQl

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:07 EST 2020

% Result     : Theorem 6.88s
% Output     : Refutation 6.88s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 208 expanded)
%              Number of leaves         :   16 (  68 expanded)
%              Depth                    :   20
%              Number of atoms          :  678 (2011 expanded)
%              Number of equality atoms :   40 ( 117 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('1',plain,(
    ! [X33: $i,X34: $i,X36: $i] :
      ( ( r2_hidden @ X33 @ ( k4_xboole_0 @ X34 @ ( k1_tarski @ X36 ) ) )
      | ( X33 = X36 )
      | ~ ( r2_hidden @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( sk_C @ X1 @ X0 )
        = X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) @ X1 )
        = X0 )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_C @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) @ X1 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( r2_hidden @ X33 @ X34 )
      | ~ ( r2_hidden @ X33 @ ( k4_xboole_0 @ X34 @ ( k1_tarski @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) @ X0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','16'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 @ X0 ) @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('22',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('23',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X33 != X35 )
      | ~ ( r2_hidden @ X33 @ ( k4_xboole_0 @ X34 @ ( k1_tarski @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('24',plain,(
    ! [X34: $i,X35: $i] :
      ~ ( r2_hidden @ X35 @ ( k4_xboole_0 @ X34 @ ( k1_tarski @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X1 ) @ X1 )
      | ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['31'])).

thf('33',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('34',plain,(
    ! [X25: $i,X26: $i,X27: $i,X29: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X25 @ X27 ) @ ( k2_zfmisc_1 @ X26 @ X29 ) )
      | ~ ( r2_hidden @ X27 @ X29 )
      | ~ ( r2_hidden @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ k1_xboole_0 @ X0 ) @ ( sk_C @ X2 @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r1_tarski @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf(t114_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = ( k2_zfmisc_1 @ B @ A ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( A = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_zfmisc_1 @ A @ B )
          = ( k2_zfmisc_1 @ B @ A ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( A = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t114_zfmisc_1])).

thf('37',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( r2_hidden @ X27 @ X28 )
      | ~ ( r2_hidden @ ( k4_tarski @ X25 @ X27 ) @ ( k2_zfmisc_1 @ X26 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('44',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('47',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['31'])).

thf('52',plain,(
    ! [X25: $i,X26: $i,X27: $i,X29: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X25 @ X27 ) @ ( k2_zfmisc_1 @ X26 @ X29 ) )
      | ~ ( r2_hidden @ X27 @ X29 )
      | ~ ( r2_hidden @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_C @ k1_xboole_0 @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ k1_xboole_0 @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( r2_hidden @ X25 @ X26 )
      | ~ ( r2_hidden @ ( k4_tarski @ X25 @ X27 ) @ ( k2_zfmisc_1 @ X26 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('62',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    $false ),
    inference(demod,[status(thm)],['49','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZTTJ2iLmQl
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:03:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 6.88/7.12  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.88/7.12  % Solved by: fo/fo7.sh
% 6.88/7.12  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.88/7.12  % done 1332 iterations in 6.637s
% 6.88/7.12  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.88/7.12  % SZS output start Refutation
% 6.88/7.12  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.88/7.12  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 6.88/7.12  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.88/7.12  thf(sk_B_type, type, sk_B: $i).
% 6.88/7.12  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 6.88/7.12  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 6.88/7.12  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.88/7.12  thf(sk_A_type, type, sk_A: $i).
% 6.88/7.12  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 6.88/7.12  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.88/7.12  thf(d3_tarski, axiom,
% 6.88/7.12    (![A:$i,B:$i]:
% 6.88/7.12     ( ( r1_tarski @ A @ B ) <=>
% 6.88/7.12       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 6.88/7.12  thf('0', plain,
% 6.88/7.12      (![X1 : $i, X3 : $i]:
% 6.88/7.12         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 6.88/7.12      inference('cnf', [status(esa)], [d3_tarski])).
% 6.88/7.12  thf(t64_zfmisc_1, axiom,
% 6.88/7.12    (![A:$i,B:$i,C:$i]:
% 6.88/7.12     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 6.88/7.12       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 6.88/7.12  thf('1', plain,
% 6.88/7.12      (![X33 : $i, X34 : $i, X36 : $i]:
% 6.88/7.12         ((r2_hidden @ X33 @ (k4_xboole_0 @ X34 @ (k1_tarski @ X36)))
% 6.88/7.12          | ((X33) = (X36))
% 6.88/7.12          | ~ (r2_hidden @ X33 @ X34))),
% 6.88/7.12      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 6.88/7.12  thf('2', plain,
% 6.88/7.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.88/7.12         ((r1_tarski @ X0 @ X1)
% 6.88/7.12          | ((sk_C @ X1 @ X0) = (X2))
% 6.88/7.12          | (r2_hidden @ (sk_C @ X1 @ X0) @ 
% 6.88/7.12             (k4_xboole_0 @ X0 @ (k1_tarski @ X2))))),
% 6.88/7.12      inference('sup-', [status(thm)], ['0', '1'])).
% 6.88/7.12  thf('3', plain,
% 6.88/7.12      (![X1 : $i, X3 : $i]:
% 6.88/7.12         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 6.88/7.12      inference('cnf', [status(esa)], [d3_tarski])).
% 6.88/7.12  thf('4', plain,
% 6.88/7.12      (![X0 : $i, X1 : $i]:
% 6.88/7.12         (((sk_C @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)) @ X1) = (X0))
% 6.88/7.12          | (r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 6.88/7.12          | (r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 6.88/7.12      inference('sup-', [status(thm)], ['2', '3'])).
% 6.88/7.12  thf('5', plain,
% 6.88/7.12      (![X0 : $i, X1 : $i]:
% 6.88/7.12         ((r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 6.88/7.12          | ((sk_C @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)) @ X1) = (X0)))),
% 6.88/7.12      inference('simplify', [status(thm)], ['4'])).
% 6.88/7.12  thf('6', plain,
% 6.88/7.12      (![X1 : $i, X3 : $i]:
% 6.88/7.12         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 6.88/7.12      inference('cnf', [status(esa)], [d3_tarski])).
% 6.88/7.12  thf('7', plain,
% 6.88/7.12      (![X0 : $i, X1 : $i]:
% 6.88/7.12         ((r2_hidden @ X0 @ X1)
% 6.88/7.12          | (r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 6.88/7.12          | (r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 6.88/7.12      inference('sup+', [status(thm)], ['5', '6'])).
% 6.88/7.12  thf('8', plain,
% 6.88/7.12      (![X0 : $i, X1 : $i]:
% 6.88/7.12         ((r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 6.88/7.12          | (r2_hidden @ X0 @ X1))),
% 6.88/7.12      inference('simplify', [status(thm)], ['7'])).
% 6.88/7.12  thf('9', plain,
% 6.88/7.12      (![X1 : $i, X3 : $i]:
% 6.88/7.12         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 6.88/7.12      inference('cnf', [status(esa)], [d3_tarski])).
% 6.88/7.12  thf('10', plain,
% 6.88/7.12      (![X33 : $i, X34 : $i, X35 : $i]:
% 6.88/7.12         ((r2_hidden @ X33 @ X34)
% 6.88/7.12          | ~ (r2_hidden @ X33 @ (k4_xboole_0 @ X34 @ (k1_tarski @ X35))))),
% 6.88/7.12      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 6.88/7.12  thf('11', plain,
% 6.88/7.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.88/7.12         ((r1_tarski @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)) @ X2)
% 6.88/7.12          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0))) @ 
% 6.88/7.12             X1))),
% 6.88/7.12      inference('sup-', [status(thm)], ['9', '10'])).
% 6.88/7.12  thf('12', plain,
% 6.88/7.12      (![X1 : $i, X3 : $i]:
% 6.88/7.12         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 6.88/7.12      inference('cnf', [status(esa)], [d3_tarski])).
% 6.88/7.12  thf('13', plain,
% 6.88/7.12      (![X0 : $i, X1 : $i]:
% 6.88/7.12         ((r1_tarski @ (k4_xboole_0 @ X0 @ (k1_tarski @ X1)) @ X0)
% 6.88/7.12          | (r1_tarski @ (k4_xboole_0 @ X0 @ (k1_tarski @ X1)) @ X0))),
% 6.88/7.12      inference('sup-', [status(thm)], ['11', '12'])).
% 6.88/7.12  thf('14', plain,
% 6.88/7.12      (![X0 : $i, X1 : $i]:
% 6.88/7.12         (r1_tarski @ (k4_xboole_0 @ X0 @ (k1_tarski @ X1)) @ X0)),
% 6.88/7.12      inference('simplify', [status(thm)], ['13'])).
% 6.88/7.12  thf(d10_xboole_0, axiom,
% 6.88/7.12    (![A:$i,B:$i]:
% 6.88/7.12     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 6.88/7.12  thf('15', plain,
% 6.88/7.12      (![X4 : $i, X6 : $i]:
% 6.88/7.12         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 6.88/7.12      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.88/7.12  thf('16', plain,
% 6.88/7.12      (![X0 : $i, X1 : $i]:
% 6.88/7.12         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 6.88/7.12          | ((X0) = (k4_xboole_0 @ X0 @ (k1_tarski @ X1))))),
% 6.88/7.12      inference('sup-', [status(thm)], ['14', '15'])).
% 6.88/7.12  thf('17', plain,
% 6.88/7.12      (![X0 : $i, X1 : $i]:
% 6.88/7.12         ((r2_hidden @ X0 @ X1)
% 6.88/7.12          | ((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 6.88/7.12      inference('sup-', [status(thm)], ['8', '16'])).
% 6.88/7.12  thf('18', plain,
% 6.88/7.12      (![X0 : $i, X1 : $i]:
% 6.88/7.12         ((r2_hidden @ X0 @ X1)
% 6.88/7.12          | ((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 6.88/7.12      inference('sup-', [status(thm)], ['8', '16'])).
% 6.88/7.12  thf('19', plain,
% 6.88/7.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.88/7.12         ((r1_tarski @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)) @ X2)
% 6.88/7.12          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0))) @ 
% 6.88/7.12             X1))),
% 6.88/7.12      inference('sup-', [status(thm)], ['9', '10'])).
% 6.88/7.12  thf('20', plain,
% 6.88/7.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.88/7.12         ((r2_hidden @ (sk_C @ X2 @ X0) @ X0)
% 6.88/7.12          | (r2_hidden @ X1 @ X0)
% 6.88/7.12          | (r1_tarski @ (k4_xboole_0 @ X0 @ (k1_tarski @ X1)) @ X2))),
% 6.88/7.12      inference('sup+', [status(thm)], ['18', '19'])).
% 6.88/7.12  thf('21', plain,
% 6.88/7.12      (![X1 : $i, X3 : $i]:
% 6.88/7.12         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 6.88/7.12      inference('cnf', [status(esa)], [d3_tarski])).
% 6.88/7.12  thf(t4_boole, axiom,
% 6.88/7.12    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 6.88/7.12  thf('22', plain,
% 6.88/7.12      (![X7 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 6.88/7.12      inference('cnf', [status(esa)], [t4_boole])).
% 6.88/7.12  thf('23', plain,
% 6.88/7.12      (![X33 : $i, X34 : $i, X35 : $i]:
% 6.88/7.12         (((X33) != (X35))
% 6.88/7.12          | ~ (r2_hidden @ X33 @ (k4_xboole_0 @ X34 @ (k1_tarski @ X35))))),
% 6.88/7.12      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 6.88/7.12  thf('24', plain,
% 6.88/7.12      (![X34 : $i, X35 : $i]:
% 6.88/7.12         ~ (r2_hidden @ X35 @ (k4_xboole_0 @ X34 @ (k1_tarski @ X35)))),
% 6.88/7.12      inference('simplify', [status(thm)], ['23'])).
% 6.88/7.12  thf('25', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 6.88/7.12      inference('sup-', [status(thm)], ['22', '24'])).
% 6.88/7.12  thf('26', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 6.88/7.12      inference('sup-', [status(thm)], ['21', '25'])).
% 6.88/7.12  thf('27', plain,
% 6.88/7.12      (![X4 : $i, X6 : $i]:
% 6.88/7.12         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 6.88/7.12      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.88/7.12  thf('28', plain,
% 6.88/7.12      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 6.88/7.12      inference('sup-', [status(thm)], ['26', '27'])).
% 6.88/7.12  thf('29', plain,
% 6.88/7.12      (![X0 : $i, X1 : $i]:
% 6.88/7.12         ((r2_hidden @ X0 @ X1)
% 6.88/7.12          | (r2_hidden @ (sk_C @ k1_xboole_0 @ X1) @ X1)
% 6.88/7.12          | ((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0)))),
% 6.88/7.12      inference('sup-', [status(thm)], ['20', '28'])).
% 6.88/7.12  thf('30', plain,
% 6.88/7.12      (![X0 : $i, X1 : $i]:
% 6.88/7.12         (((X0) = (k1_xboole_0))
% 6.88/7.12          | (r2_hidden @ X1 @ X0)
% 6.88/7.12          | (r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ X0)
% 6.88/7.12          | (r2_hidden @ X1 @ X0))),
% 6.88/7.12      inference('sup+', [status(thm)], ['17', '29'])).
% 6.88/7.12  thf('31', plain,
% 6.88/7.12      (![X0 : $i, X1 : $i]:
% 6.88/7.12         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ X0)
% 6.88/7.12          | (r2_hidden @ X1 @ X0)
% 6.88/7.12          | ((X0) = (k1_xboole_0)))),
% 6.88/7.12      inference('simplify', [status(thm)], ['30'])).
% 6.88/7.12  thf('32', plain,
% 6.88/7.12      (![X0 : $i]:
% 6.88/7.12         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ X0) | ((X0) = (k1_xboole_0)))),
% 6.88/7.12      inference('condensation', [status(thm)], ['31'])).
% 6.88/7.12  thf('33', plain,
% 6.88/7.12      (![X1 : $i, X3 : $i]:
% 6.88/7.12         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 6.88/7.12      inference('cnf', [status(esa)], [d3_tarski])).
% 6.88/7.12  thf(l54_zfmisc_1, axiom,
% 6.88/7.12    (![A:$i,B:$i,C:$i,D:$i]:
% 6.88/7.12     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 6.88/7.12       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 6.88/7.12  thf('34', plain,
% 6.88/7.12      (![X25 : $i, X26 : $i, X27 : $i, X29 : $i]:
% 6.88/7.12         ((r2_hidden @ (k4_tarski @ X25 @ X27) @ (k2_zfmisc_1 @ X26 @ X29))
% 6.88/7.12          | ~ (r2_hidden @ X27 @ X29)
% 6.88/7.12          | ~ (r2_hidden @ X25 @ X26))),
% 6.88/7.12      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 6.88/7.12  thf('35', plain,
% 6.88/7.12      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.88/7.12         ((r1_tarski @ X0 @ X1)
% 6.88/7.12          | ~ (r2_hidden @ X3 @ X2)
% 6.88/7.12          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 6.88/7.12             (k2_zfmisc_1 @ X2 @ X0)))),
% 6.88/7.12      inference('sup-', [status(thm)], ['33', '34'])).
% 6.88/7.12  thf('36', plain,
% 6.88/7.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.88/7.12         (((X0) = (k1_xboole_0))
% 6.88/7.12          | (r2_hidden @ 
% 6.88/7.12             (k4_tarski @ (sk_C @ k1_xboole_0 @ X0) @ (sk_C @ X2 @ X1)) @ 
% 6.88/7.12             (k2_zfmisc_1 @ X0 @ X1))
% 6.88/7.12          | (r1_tarski @ X1 @ X2))),
% 6.88/7.12      inference('sup-', [status(thm)], ['32', '35'])).
% 6.88/7.12  thf(t114_zfmisc_1, conjecture,
% 6.88/7.12    (![A:$i,B:$i]:
% 6.88/7.12     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 6.88/7.12       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 6.88/7.12         ( ( A ) = ( B ) ) ) ))).
% 6.88/7.12  thf(zf_stmt_0, negated_conjecture,
% 6.88/7.12    (~( ![A:$i,B:$i]:
% 6.88/7.12        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 6.88/7.12          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 6.88/7.12            ( ( A ) = ( B ) ) ) ) )),
% 6.88/7.12    inference('cnf.neg', [status(esa)], [t114_zfmisc_1])).
% 6.88/7.12  thf('37', plain,
% 6.88/7.12      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_B @ sk_A))),
% 6.88/7.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.88/7.12  thf('38', plain,
% 6.88/7.12      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 6.88/7.12         ((r2_hidden @ X27 @ X28)
% 6.88/7.12          | ~ (r2_hidden @ (k4_tarski @ X25 @ X27) @ (k2_zfmisc_1 @ X26 @ X28)))),
% 6.88/7.12      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 6.88/7.12  thf('39', plain,
% 6.88/7.12      (![X0 : $i, X1 : $i]:
% 6.88/7.12         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 6.88/7.12          | (r2_hidden @ X0 @ sk_A))),
% 6.88/7.12      inference('sup-', [status(thm)], ['37', '38'])).
% 6.88/7.12  thf('40', plain,
% 6.88/7.12      (![X0 : $i]:
% 6.88/7.12         ((r1_tarski @ sk_B @ X0)
% 6.88/7.12          | ((sk_A) = (k1_xboole_0))
% 6.88/7.12          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 6.88/7.12      inference('sup-', [status(thm)], ['36', '39'])).
% 6.88/7.12  thf('41', plain, (((sk_A) != (k1_xboole_0))),
% 6.88/7.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.88/7.12  thf('42', plain,
% 6.88/7.12      (![X0 : $i]:
% 6.88/7.12         ((r1_tarski @ sk_B @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 6.88/7.12      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 6.88/7.12  thf('43', plain,
% 6.88/7.12      (![X1 : $i, X3 : $i]:
% 6.88/7.12         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 6.88/7.12      inference('cnf', [status(esa)], [d3_tarski])).
% 6.88/7.12  thf('44', plain, (((r1_tarski @ sk_B @ sk_A) | (r1_tarski @ sk_B @ sk_A))),
% 6.88/7.12      inference('sup-', [status(thm)], ['42', '43'])).
% 6.88/7.12  thf('45', plain, ((r1_tarski @ sk_B @ sk_A)),
% 6.88/7.12      inference('simplify', [status(thm)], ['44'])).
% 6.88/7.12  thf('46', plain,
% 6.88/7.12      (![X4 : $i, X6 : $i]:
% 6.88/7.12         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 6.88/7.12      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.88/7.12  thf('47', plain, ((~ (r1_tarski @ sk_A @ sk_B) | ((sk_A) = (sk_B)))),
% 6.88/7.12      inference('sup-', [status(thm)], ['45', '46'])).
% 6.88/7.12  thf('48', plain, (((sk_A) != (sk_B))),
% 6.88/7.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.88/7.12  thf('49', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 6.88/7.12      inference('simplify_reflect-', [status(thm)], ['47', '48'])).
% 6.88/7.12  thf('50', plain,
% 6.88/7.12      (![X1 : $i, X3 : $i]:
% 6.88/7.12         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 6.88/7.12      inference('cnf', [status(esa)], [d3_tarski])).
% 6.88/7.12  thf('51', plain,
% 6.88/7.12      (![X0 : $i]:
% 6.88/7.12         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ X0) | ((X0) = (k1_xboole_0)))),
% 6.88/7.12      inference('condensation', [status(thm)], ['31'])).
% 6.88/7.12  thf('52', plain,
% 6.88/7.12      (![X25 : $i, X26 : $i, X27 : $i, X29 : $i]:
% 6.88/7.12         ((r2_hidden @ (k4_tarski @ X25 @ X27) @ (k2_zfmisc_1 @ X26 @ X29))
% 6.88/7.12          | ~ (r2_hidden @ X27 @ X29)
% 6.88/7.12          | ~ (r2_hidden @ X25 @ X26))),
% 6.88/7.12      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 6.88/7.12  thf('53', plain,
% 6.88/7.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.88/7.12         (((X0) = (k1_xboole_0))
% 6.88/7.12          | ~ (r2_hidden @ X2 @ X1)
% 6.88/7.12          | (r2_hidden @ (k4_tarski @ X2 @ (sk_C @ k1_xboole_0 @ X0)) @ 
% 6.88/7.12             (k2_zfmisc_1 @ X1 @ X0)))),
% 6.88/7.12      inference('sup-', [status(thm)], ['51', '52'])).
% 6.88/7.12  thf('54', plain,
% 6.88/7.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.88/7.12         ((r1_tarski @ X0 @ X1)
% 6.88/7.12          | (r2_hidden @ 
% 6.88/7.12             (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_C @ k1_xboole_0 @ X2)) @ 
% 6.88/7.12             (k2_zfmisc_1 @ X0 @ X2))
% 6.88/7.12          | ((X2) = (k1_xboole_0)))),
% 6.88/7.12      inference('sup-', [status(thm)], ['50', '53'])).
% 6.88/7.12  thf('55', plain,
% 6.88/7.12      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_B @ sk_A))),
% 6.88/7.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.88/7.12  thf('56', plain,
% 6.88/7.12      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 6.88/7.12         ((r2_hidden @ X25 @ X26)
% 6.88/7.12          | ~ (r2_hidden @ (k4_tarski @ X25 @ X27) @ (k2_zfmisc_1 @ X26 @ X28)))),
% 6.88/7.12      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 6.88/7.12  thf('57', plain,
% 6.88/7.12      (![X0 : $i, X1 : $i]:
% 6.88/7.12         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 6.88/7.12          | (r2_hidden @ X1 @ sk_B))),
% 6.88/7.12      inference('sup-', [status(thm)], ['55', '56'])).
% 6.88/7.12  thf('58', plain,
% 6.88/7.12      (![X0 : $i]:
% 6.88/7.12         (((sk_B) = (k1_xboole_0))
% 6.88/7.12          | (r1_tarski @ sk_A @ X0)
% 6.88/7.12          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 6.88/7.12      inference('sup-', [status(thm)], ['54', '57'])).
% 6.88/7.12  thf('59', plain, (((sk_B) != (k1_xboole_0))),
% 6.88/7.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.88/7.12  thf('60', plain,
% 6.88/7.12      (![X0 : $i]:
% 6.88/7.12         ((r1_tarski @ sk_A @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 6.88/7.12      inference('simplify_reflect-', [status(thm)], ['58', '59'])).
% 6.88/7.12  thf('61', plain,
% 6.88/7.12      (![X1 : $i, X3 : $i]:
% 6.88/7.12         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 6.88/7.12      inference('cnf', [status(esa)], [d3_tarski])).
% 6.88/7.12  thf('62', plain, (((r1_tarski @ sk_A @ sk_B) | (r1_tarski @ sk_A @ sk_B))),
% 6.88/7.12      inference('sup-', [status(thm)], ['60', '61'])).
% 6.88/7.12  thf('63', plain, ((r1_tarski @ sk_A @ sk_B)),
% 6.88/7.12      inference('simplify', [status(thm)], ['62'])).
% 6.88/7.12  thf('64', plain, ($false), inference('demod', [status(thm)], ['49', '63'])).
% 6.88/7.12  
% 6.88/7.12  % SZS output end Refutation
% 6.88/7.12  
% 6.88/7.13  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
