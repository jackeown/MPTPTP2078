%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Dctu6ZiEem

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:47 EST 2020

% Result     : Theorem 2.53s
% Output     : Refutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 248 expanded)
%              Number of leaves         :   37 (  92 expanded)
%              Depth                    :   19
%              Number of atoms          :  744 (1488 expanded)
%              Number of equality atoms :   76 ( 134 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X61: $i] :
      ( ( ( k3_relat_1 @ X61 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X61 ) @ ( k2_relat_1 @ X61 ) ) )
      | ~ ( v1_relat_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t37_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X8: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X8 @ X10 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('9',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( X48 != X50 )
      | ~ ( r2_hidden @ X48 @ ( k4_xboole_0 @ X49 @ ( k1_tarski @ X50 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('10',plain,(
    ! [X49: $i,X50: $i] :
      ~ ( r2_hidden @ X50 @ ( k4_xboole_0 @ X49 @ ( k1_tarski @ X50 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['2','11'])).

thf('13',plain,(
    ! [X8: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X8 @ X10 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('17',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ X1 @ k1_xboole_0 )
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','18'])).

thf(fc10_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('20',plain,(
    ! [X63: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X63 ) )
      | ~ ( v1_xboole_0 @ X63 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

thf('21',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ X1 @ k1_xboole_0 )
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','18'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('24',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('25',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('26',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t63_relat_1,conjecture,
    ( ( k3_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf(zf_stmt_0,negated_conjecture,(
    ( k3_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('cnf.neg',[status(esa)],[t63_relat_1])).

thf('27',plain,(
    ( k3_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_relat_1 @ ( k5_xboole_0 @ X0 @ X0 ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_relat_1 @ ( k5_xboole_0 @ X1 @ X1 ) )
     != ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_relat_1 @ k1_xboole_0 )
     != ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k3_relat_1 @ k1_xboole_0 )
       != ( k2_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('33',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k3_relat_1 @ k1_xboole_0 )
       != ( k5_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_relat_1 @ k1_xboole_0 )
       != ( k5_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_relat_1 @ k1_xboole_0 )
       != ( k2_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','38'])).

thf(rc1_xboole_0,axiom,(
    ? [A: $i] :
      ( v1_xboole_0 @ A ) )).

thf('40',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('41',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('42',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('43',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_relat_1 @ k1_xboole_0 )
       != ( k2_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['39','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k3_relat_1 @ k1_xboole_0 )
       != ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','45'])).

thf('47',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['46'])).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['40','43'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('49',plain,(
    ! [X58: $i] :
      ( ( v1_relat_1 @ X58 )
      | ( r2_hidden @ ( sk_B @ X58 ) @ X58 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('50',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('51',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['47','48','51'])).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['40','43'])).

thf('54',plain,(
    ! [X63: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X63 ) )
      | ~ ( v1_xboole_0 @ X63 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('55',plain,(
    ! [X65: $i] :
      ( ( ( k1_relat_1 @ X65 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X65 ) ) )
      | ~ ( v1_relat_1 @ X65 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('56',plain,(
    ! [X64: $i] :
      ( ( r1_tarski @ X64 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X64 ) @ ( k2_relat_1 @ X64 ) ) )
      | ~ ( v1_relat_1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k4_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('58',plain,(
    ! [X62: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X62 ) )
      | ~ ( v1_relat_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k4_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('61',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('62',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf(t125_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('64',plain,(
    ! [X44: $i,X46: $i,X47: $i] :
      ( ( k2_zfmisc_1 @ X47 @ ( k4_xboole_0 @ X44 @ X46 ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X47 @ X44 ) @ ( k2_zfmisc_1 @ X47 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('67',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('68',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('71',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11 = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k4_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','74'])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('76',plain,(
    ! [X55: $i] :
      ( ( v1_relat_1 @ X55 )
      | ~ ( v1_xboole_0 @ X55 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X65: $i] :
      ( ( ( k2_relat_1 @ X65 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X65 ) ) )
      | ~ ( v1_relat_1 @ X65 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['40','43'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X55: $i] :
      ( ( v1_relat_1 @ X55 )
      | ~ ( v1_xboole_0 @ X55 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['53','85'])).

thf('87',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['40','43'])).

thf('88',plain,(
    $false ),
    inference(demod,[status(thm)],['52','86','87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Dctu6ZiEem
% 0.17/0.37  % Computer   : n009.cluster.edu
% 0.17/0.37  % Model      : x86_64 x86_64
% 0.17/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.37  % Memory     : 8042.1875MB
% 0.17/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.37  % CPULimit   : 60
% 0.17/0.37  % DateTime   : Tue Dec  1 10:20:11 EST 2020
% 0.17/0.37  % CPUTime    : 
% 0.17/0.37  % Running portfolio for 600 s
% 0.17/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.37  % Number of cores: 8
% 0.17/0.37  % Python version: Python 3.6.8
% 0.17/0.37  % Running in FO mode
% 2.53/2.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.53/2.73  % Solved by: fo/fo7.sh
% 2.53/2.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.53/2.73  % done 6591 iterations in 2.248s
% 2.53/2.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.53/2.73  % SZS output start Refutation
% 2.53/2.73  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.53/2.73  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.53/2.73  thf(sk_B_type, type, sk_B: $i > $i).
% 2.53/2.73  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.53/2.73  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 2.53/2.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.53/2.73  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.53/2.73  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 2.53/2.73  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.53/2.73  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 2.53/2.73  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.53/2.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.53/2.73  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 2.53/2.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.53/2.73  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.53/2.73  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.53/2.73  thf(sk_A_type, type, sk_A: $i).
% 2.53/2.73  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.53/2.73  thf(d6_relat_1, axiom,
% 2.53/2.73    (![A:$i]:
% 2.53/2.73     ( ( v1_relat_1 @ A ) =>
% 2.53/2.73       ( ( k3_relat_1 @ A ) =
% 2.53/2.73         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 2.53/2.73  thf('0', plain,
% 2.53/2.73      (![X61 : $i]:
% 2.53/2.73         (((k3_relat_1 @ X61)
% 2.53/2.73            = (k2_xboole_0 @ (k1_relat_1 @ X61) @ (k2_relat_1 @ X61)))
% 2.53/2.73          | ~ (v1_relat_1 @ X61))),
% 2.53/2.73      inference('cnf', [status(esa)], [d6_relat_1])).
% 2.53/2.73  thf(l13_xboole_0, axiom,
% 2.53/2.73    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 2.53/2.73  thf('1', plain,
% 2.53/2.73      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 2.53/2.73      inference('cnf', [status(esa)], [l13_xboole_0])).
% 2.53/2.73  thf(d3_tarski, axiom,
% 2.53/2.73    (![A:$i,B:$i]:
% 2.53/2.73     ( ( r1_tarski @ A @ B ) <=>
% 2.53/2.73       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.53/2.73  thf('2', plain,
% 2.53/2.73      (![X1 : $i, X3 : $i]:
% 2.53/2.73         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 2.53/2.73      inference('cnf', [status(esa)], [d3_tarski])).
% 2.53/2.73  thf('3', plain,
% 2.53/2.73      (![X1 : $i, X3 : $i]:
% 2.53/2.73         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 2.53/2.73      inference('cnf', [status(esa)], [d3_tarski])).
% 2.53/2.73  thf('4', plain,
% 2.53/2.73      (![X1 : $i, X3 : $i]:
% 2.53/2.73         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 2.53/2.73      inference('cnf', [status(esa)], [d3_tarski])).
% 2.53/2.73  thf('5', plain,
% 2.53/2.73      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 2.53/2.73      inference('sup-', [status(thm)], ['3', '4'])).
% 2.53/2.73  thf('6', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 2.53/2.73      inference('simplify', [status(thm)], ['5'])).
% 2.53/2.73  thf(t37_xboole_1, axiom,
% 2.53/2.73    (![A:$i,B:$i]:
% 2.53/2.73     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.53/2.73  thf('7', plain,
% 2.53/2.73      (![X8 : $i, X10 : $i]:
% 2.53/2.73         (((k4_xboole_0 @ X8 @ X10) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ X10))),
% 2.53/2.73      inference('cnf', [status(esa)], [t37_xboole_1])).
% 2.53/2.73  thf('8', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.53/2.73      inference('sup-', [status(thm)], ['6', '7'])).
% 2.53/2.73  thf(t64_zfmisc_1, axiom,
% 2.53/2.73    (![A:$i,B:$i,C:$i]:
% 2.53/2.73     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 2.53/2.73       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 2.53/2.73  thf('9', plain,
% 2.53/2.73      (![X48 : $i, X49 : $i, X50 : $i]:
% 2.53/2.73         (((X48) != (X50))
% 2.53/2.73          | ~ (r2_hidden @ X48 @ (k4_xboole_0 @ X49 @ (k1_tarski @ X50))))),
% 2.53/2.73      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 2.53/2.73  thf('10', plain,
% 2.53/2.73      (![X49 : $i, X50 : $i]:
% 2.53/2.73         ~ (r2_hidden @ X50 @ (k4_xboole_0 @ X49 @ (k1_tarski @ X50)))),
% 2.53/2.73      inference('simplify', [status(thm)], ['9'])).
% 2.53/2.73  thf('11', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 2.53/2.73      inference('sup-', [status(thm)], ['8', '10'])).
% 2.53/2.73  thf('12', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 2.53/2.73      inference('sup-', [status(thm)], ['2', '11'])).
% 2.53/2.73  thf('13', plain,
% 2.53/2.73      (![X8 : $i, X10 : $i]:
% 2.53/2.73         (((k4_xboole_0 @ X8 @ X10) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ X10))),
% 2.53/2.73      inference('cnf', [status(esa)], [t37_xboole_1])).
% 2.53/2.73  thf('14', plain,
% 2.53/2.73      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 2.53/2.73      inference('sup-', [status(thm)], ['12', '13'])).
% 2.53/2.73  thf(d6_xboole_0, axiom,
% 2.53/2.73    (![A:$i,B:$i]:
% 2.53/2.73     ( ( k5_xboole_0 @ A @ B ) =
% 2.53/2.73       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 2.53/2.73  thf('15', plain,
% 2.53/2.73      (![X4 : $i, X5 : $i]:
% 2.53/2.73         ((k5_xboole_0 @ X4 @ X5)
% 2.53/2.73           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 2.53/2.73      inference('cnf', [status(esa)], [d6_xboole_0])).
% 2.53/2.73  thf('16', plain,
% 2.53/2.73      (![X0 : $i]:
% 2.53/2.73         ((k5_xboole_0 @ X0 @ k1_xboole_0)
% 2.53/2.73           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 2.53/2.73      inference('sup+', [status(thm)], ['14', '15'])).
% 2.53/2.73  thf(t3_boole, axiom,
% 2.53/2.73    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.53/2.73  thf('17', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 2.53/2.73      inference('cnf', [status(esa)], [t3_boole])).
% 2.53/2.73  thf('18', plain,
% 2.53/2.73      (![X0 : $i]:
% 2.53/2.73         ((k5_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 2.53/2.73      inference('demod', [status(thm)], ['16', '17'])).
% 2.53/2.73  thf('19', plain,
% 2.53/2.73      (![X0 : $i, X1 : $i]:
% 2.53/2.73         (((k5_xboole_0 @ X1 @ k1_xboole_0) = (k2_xboole_0 @ X1 @ X0))
% 2.53/2.73          | ~ (v1_xboole_0 @ X0))),
% 2.53/2.73      inference('sup+', [status(thm)], ['1', '18'])).
% 2.53/2.73  thf(fc10_relat_1, axiom,
% 2.53/2.73    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ))).
% 2.53/2.73  thf('20', plain,
% 2.53/2.73      (![X63 : $i]:
% 2.53/2.73         ((v1_xboole_0 @ (k1_relat_1 @ X63)) | ~ (v1_xboole_0 @ X63))),
% 2.53/2.73      inference('cnf', [status(esa)], [fc10_relat_1])).
% 2.53/2.73  thf('21', plain,
% 2.53/2.73      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 2.53/2.73      inference('cnf', [status(esa)], [l13_xboole_0])).
% 2.53/2.73  thf('22', plain,
% 2.53/2.73      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 2.53/2.73      inference('sup-', [status(thm)], ['20', '21'])).
% 2.53/2.73  thf('23', plain,
% 2.53/2.73      (![X0 : $i, X1 : $i]:
% 2.53/2.73         (((k5_xboole_0 @ X1 @ k1_xboole_0) = (k2_xboole_0 @ X1 @ X0))
% 2.53/2.73          | ~ (v1_xboole_0 @ X0))),
% 2.53/2.73      inference('sup+', [status(thm)], ['1', '18'])).
% 2.53/2.73  thf(t92_xboole_1, axiom,
% 2.53/2.73    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 2.53/2.73  thf('24', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ X18) = (k1_xboole_0))),
% 2.53/2.73      inference('cnf', [status(esa)], [t92_xboole_1])).
% 2.53/2.73  thf('25', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ X18) = (k1_xboole_0))),
% 2.53/2.73      inference('cnf', [status(esa)], [t92_xboole_1])).
% 2.53/2.73  thf('26', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ X18) = (k1_xboole_0))),
% 2.53/2.73      inference('cnf', [status(esa)], [t92_xboole_1])).
% 2.53/2.73  thf(t63_relat_1, conjecture,
% 2.53/2.73    (( k3_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 2.53/2.73  thf(zf_stmt_0, negated_conjecture,
% 2.53/2.73    (( k3_relat_1 @ k1_xboole_0 ) != ( k1_xboole_0 )),
% 2.53/2.73    inference('cnf.neg', [status(esa)], [t63_relat_1])).
% 2.53/2.73  thf('27', plain, (((k3_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 2.53/2.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.73  thf('28', plain,
% 2.53/2.73      (![X0 : $i]: ((k3_relat_1 @ (k5_xboole_0 @ X0 @ X0)) != (k1_xboole_0))),
% 2.53/2.73      inference('sup-', [status(thm)], ['26', '27'])).
% 2.53/2.73  thf('29', plain,
% 2.53/2.73      (![X0 : $i, X1 : $i]:
% 2.53/2.73         ((k3_relat_1 @ (k5_xboole_0 @ X1 @ X1)) != (k5_xboole_0 @ X0 @ X0))),
% 2.53/2.73      inference('sup-', [status(thm)], ['25', '28'])).
% 2.53/2.73  thf('30', plain,
% 2.53/2.73      (![X0 : $i]: ((k3_relat_1 @ k1_xboole_0) != (k5_xboole_0 @ X0 @ X0))),
% 2.53/2.73      inference('sup-', [status(thm)], ['24', '29'])).
% 2.53/2.73  thf('31', plain,
% 2.53/2.73      (![X0 : $i]:
% 2.53/2.73         (((k3_relat_1 @ k1_xboole_0) != (k2_xboole_0 @ k1_xboole_0 @ X0))
% 2.53/2.73          | ~ (v1_xboole_0 @ X0))),
% 2.53/2.73      inference('sup-', [status(thm)], ['23', '30'])).
% 2.53/2.73  thf('32', plain,
% 2.53/2.73      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 2.53/2.73      inference('sup-', [status(thm)], ['12', '13'])).
% 2.53/2.73  thf('33', plain,
% 2.53/2.73      (![X4 : $i, X5 : $i]:
% 2.53/2.73         ((k5_xboole_0 @ X4 @ X5)
% 2.53/2.73           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 2.53/2.73      inference('cnf', [status(esa)], [d6_xboole_0])).
% 2.53/2.73  thf('34', plain,
% 2.53/2.73      (![X0 : $i]:
% 2.53/2.73         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 2.53/2.73           = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 2.53/2.73      inference('sup+', [status(thm)], ['32', '33'])).
% 2.53/2.73  thf('35', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 2.53/2.73      inference('cnf', [status(esa)], [t3_boole])).
% 2.53/2.73  thf('36', plain,
% 2.53/2.73      (![X0 : $i]:
% 2.53/2.73         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 2.53/2.73      inference('demod', [status(thm)], ['34', '35'])).
% 2.53/2.73  thf('37', plain,
% 2.53/2.73      (![X0 : $i]:
% 2.53/2.73         (((k3_relat_1 @ k1_xboole_0) != (k5_xboole_0 @ k1_xboole_0 @ X0))
% 2.53/2.73          | ~ (v1_xboole_0 @ X0))),
% 2.53/2.73      inference('demod', [status(thm)], ['31', '36'])).
% 2.53/2.73  thf('38', plain,
% 2.53/2.73      (![X0 : $i, X1 : $i]:
% 2.53/2.73         (((k3_relat_1 @ k1_xboole_0) != (k5_xboole_0 @ (k1_relat_1 @ X0) @ X1))
% 2.53/2.73          | ~ (v1_xboole_0 @ X0)
% 2.53/2.73          | ~ (v1_xboole_0 @ X1))),
% 2.53/2.73      inference('sup-', [status(thm)], ['22', '37'])).
% 2.53/2.73  thf('39', plain,
% 2.53/2.73      (![X0 : $i, X1 : $i]:
% 2.53/2.73         (((k3_relat_1 @ k1_xboole_0) != (k2_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 2.53/2.73          | ~ (v1_xboole_0 @ X0)
% 2.53/2.73          | ~ (v1_xboole_0 @ k1_xboole_0)
% 2.53/2.73          | ~ (v1_xboole_0 @ X1))),
% 2.53/2.73      inference('sup-', [status(thm)], ['19', '38'])).
% 2.53/2.73  thf(rc1_xboole_0, axiom, (?[A:$i]: ( v1_xboole_0 @ A ))).
% 2.53/2.73  thf('40', plain, ((v1_xboole_0 @ sk_A)),
% 2.53/2.73      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 2.53/2.73  thf('41', plain, ((v1_xboole_0 @ sk_A)),
% 2.53/2.73      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 2.53/2.73  thf('42', plain,
% 2.53/2.73      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 2.53/2.73      inference('cnf', [status(esa)], [l13_xboole_0])).
% 2.53/2.73  thf('43', plain, (((sk_A) = (k1_xboole_0))),
% 2.53/2.73      inference('sup-', [status(thm)], ['41', '42'])).
% 2.53/2.73  thf('44', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.53/2.73      inference('demod', [status(thm)], ['40', '43'])).
% 2.53/2.73  thf('45', plain,
% 2.53/2.73      (![X0 : $i, X1 : $i]:
% 2.53/2.73         (((k3_relat_1 @ k1_xboole_0) != (k2_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 2.53/2.73          | ~ (v1_xboole_0 @ X0)
% 2.53/2.73          | ~ (v1_xboole_0 @ X1))),
% 2.53/2.73      inference('demod', [status(thm)], ['39', '44'])).
% 2.53/2.73  thf('46', plain,
% 2.53/2.73      (![X0 : $i]:
% 2.53/2.73         (((k3_relat_1 @ k1_xboole_0) != (k3_relat_1 @ X0))
% 2.53/2.73          | ~ (v1_relat_1 @ X0)
% 2.53/2.73          | ~ (v1_xboole_0 @ X0)
% 2.53/2.73          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0)))),
% 2.53/2.73      inference('sup-', [status(thm)], ['0', '45'])).
% 2.53/2.73  thf('47', plain,
% 2.53/2.73      ((~ (v1_xboole_0 @ (k2_relat_1 @ k1_xboole_0))
% 2.53/2.73        | ~ (v1_xboole_0 @ k1_xboole_0)
% 2.53/2.73        | ~ (v1_relat_1 @ k1_xboole_0))),
% 2.53/2.73      inference('eq_res', [status(thm)], ['46'])).
% 2.53/2.73  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.53/2.73      inference('demod', [status(thm)], ['40', '43'])).
% 2.53/2.73  thf(d1_relat_1, axiom,
% 2.53/2.73    (![A:$i]:
% 2.53/2.73     ( ( v1_relat_1 @ A ) <=>
% 2.53/2.73       ( ![B:$i]:
% 2.53/2.73         ( ~( ( r2_hidden @ B @ A ) & 
% 2.53/2.73              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 2.53/2.73  thf('49', plain,
% 2.53/2.73      (![X58 : $i]: ((v1_relat_1 @ X58) | (r2_hidden @ (sk_B @ X58) @ X58))),
% 2.53/2.73      inference('cnf', [status(esa)], [d1_relat_1])).
% 2.53/2.73  thf('50', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 2.53/2.73      inference('sup-', [status(thm)], ['8', '10'])).
% 2.53/2.73  thf('51', plain, ((v1_relat_1 @ k1_xboole_0)),
% 2.53/2.73      inference('sup-', [status(thm)], ['49', '50'])).
% 2.53/2.73  thf('52', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ k1_xboole_0))),
% 2.53/2.73      inference('demod', [status(thm)], ['47', '48', '51'])).
% 2.53/2.73  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.53/2.73      inference('demod', [status(thm)], ['40', '43'])).
% 2.53/2.73  thf('54', plain,
% 2.53/2.73      (![X63 : $i]:
% 2.53/2.73         ((v1_xboole_0 @ (k1_relat_1 @ X63)) | ~ (v1_xboole_0 @ X63))),
% 2.53/2.73      inference('cnf', [status(esa)], [fc10_relat_1])).
% 2.53/2.73  thf(t37_relat_1, axiom,
% 2.53/2.73    (![A:$i]:
% 2.53/2.73     ( ( v1_relat_1 @ A ) =>
% 2.53/2.73       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 2.53/2.73         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 2.53/2.73  thf('55', plain,
% 2.53/2.73      (![X65 : $i]:
% 2.53/2.73         (((k1_relat_1 @ X65) = (k2_relat_1 @ (k4_relat_1 @ X65)))
% 2.53/2.73          | ~ (v1_relat_1 @ X65))),
% 2.53/2.73      inference('cnf', [status(esa)], [t37_relat_1])).
% 2.53/2.73  thf(t21_relat_1, axiom,
% 2.53/2.73    (![A:$i]:
% 2.53/2.73     ( ( v1_relat_1 @ A ) =>
% 2.53/2.73       ( r1_tarski @
% 2.53/2.73         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 2.53/2.73  thf('56', plain,
% 2.53/2.73      (![X64 : $i]:
% 2.53/2.73         ((r1_tarski @ X64 @ 
% 2.53/2.73           (k2_zfmisc_1 @ (k1_relat_1 @ X64) @ (k2_relat_1 @ X64)))
% 2.53/2.73          | ~ (v1_relat_1 @ X64))),
% 2.53/2.73      inference('cnf', [status(esa)], [t21_relat_1])).
% 2.53/2.73  thf('57', plain,
% 2.53/2.73      (![X0 : $i]:
% 2.53/2.73         ((r1_tarski @ (k4_relat_1 @ X0) @ 
% 2.53/2.73           (k2_zfmisc_1 @ (k1_relat_1 @ (k4_relat_1 @ X0)) @ (k1_relat_1 @ X0)))
% 2.53/2.73          | ~ (v1_relat_1 @ X0)
% 2.53/2.73          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 2.53/2.73      inference('sup+', [status(thm)], ['55', '56'])).
% 2.53/2.73  thf(dt_k4_relat_1, axiom,
% 2.53/2.73    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 2.53/2.73  thf('58', plain,
% 2.53/2.73      (![X62 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X62)) | ~ (v1_relat_1 @ X62))),
% 2.53/2.73      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 2.53/2.73  thf('59', plain,
% 2.53/2.73      (![X0 : $i]:
% 2.53/2.73         (~ (v1_relat_1 @ X0)
% 2.53/2.73          | (r1_tarski @ (k4_relat_1 @ X0) @ 
% 2.53/2.73             (k2_zfmisc_1 @ (k1_relat_1 @ (k4_relat_1 @ X0)) @ 
% 2.53/2.73              (k1_relat_1 @ X0))))),
% 2.53/2.73      inference('clc', [status(thm)], ['57', '58'])).
% 2.53/2.73  thf('60', plain,
% 2.53/2.73      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 2.53/2.73      inference('cnf', [status(esa)], [l13_xboole_0])).
% 2.53/2.73  thf('61', plain,
% 2.53/2.73      (![X4 : $i, X5 : $i]:
% 2.53/2.73         ((k5_xboole_0 @ X4 @ X5)
% 2.53/2.73           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 2.53/2.73      inference('cnf', [status(esa)], [d6_xboole_0])).
% 2.53/2.73  thf(idempotence_k2_xboole_0, axiom,
% 2.53/2.73    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 2.53/2.73  thf('62', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ X6) = (X6))),
% 2.53/2.73      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 2.53/2.73  thf('63', plain,
% 2.53/2.73      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 2.53/2.73      inference('sup+', [status(thm)], ['61', '62'])).
% 2.53/2.73  thf(t125_zfmisc_1, axiom,
% 2.53/2.73    (![A:$i,B:$i,C:$i]:
% 2.53/2.73     ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) ) =
% 2.53/2.73         ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 2.53/2.73       ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 2.53/2.73         ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 2.53/2.73  thf('64', plain,
% 2.53/2.73      (![X44 : $i, X46 : $i, X47 : $i]:
% 2.53/2.73         ((k2_zfmisc_1 @ X47 @ (k4_xboole_0 @ X44 @ X46))
% 2.53/2.73           = (k4_xboole_0 @ (k2_zfmisc_1 @ X47 @ X44) @ 
% 2.53/2.73              (k2_zfmisc_1 @ X47 @ X46)))),
% 2.53/2.73      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 2.53/2.73  thf('65', plain,
% 2.53/2.73      (![X0 : $i, X1 : $i]:
% 2.53/2.73         ((k2_zfmisc_1 @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 2.53/2.73           = (k5_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 2.53/2.73      inference('sup+', [status(thm)], ['63', '64'])).
% 2.53/2.73  thf('66', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.53/2.73      inference('sup-', [status(thm)], ['6', '7'])).
% 2.53/2.73  thf('67', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ X18) = (k1_xboole_0))),
% 2.53/2.73      inference('cnf', [status(esa)], [t92_xboole_1])).
% 2.53/2.73  thf('68', plain,
% 2.53/2.73      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.53/2.73      inference('demod', [status(thm)], ['65', '66', '67'])).
% 2.53/2.73  thf('69', plain,
% 2.53/2.73      (![X0 : $i, X1 : $i]:
% 2.53/2.73         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.53/2.73      inference('sup+', [status(thm)], ['60', '68'])).
% 2.53/2.73  thf('70', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.53/2.73      inference('sup-', [status(thm)], ['6', '7'])).
% 2.53/2.73  thf(t38_xboole_1, axiom,
% 2.53/2.73    (![A:$i,B:$i]:
% 2.53/2.73     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 2.53/2.73       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 2.53/2.73  thf('71', plain,
% 2.53/2.73      (![X11 : $i, X12 : $i]:
% 2.53/2.73         (((X11) = (k1_xboole_0))
% 2.53/2.73          | ~ (r1_tarski @ X11 @ (k4_xboole_0 @ X12 @ X11)))),
% 2.53/2.73      inference('cnf', [status(esa)], [t38_xboole_1])).
% 2.53/2.73  thf('72', plain,
% 2.53/2.73      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 2.53/2.73      inference('sup-', [status(thm)], ['70', '71'])).
% 2.53/2.73  thf('73', plain,
% 2.53/2.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.53/2.73         (~ (r1_tarski @ X2 @ (k2_zfmisc_1 @ X1 @ X0))
% 2.53/2.73          | ~ (v1_xboole_0 @ X0)
% 2.53/2.73          | ((X2) = (k1_xboole_0)))),
% 2.53/2.73      inference('sup-', [status(thm)], ['69', '72'])).
% 2.53/2.73  thf('74', plain,
% 2.53/2.73      (![X0 : $i]:
% 2.53/2.73         (~ (v1_relat_1 @ X0)
% 2.53/2.73          | ((k4_relat_1 @ X0) = (k1_xboole_0))
% 2.53/2.73          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 2.53/2.73      inference('sup-', [status(thm)], ['59', '73'])).
% 2.53/2.73  thf('75', plain,
% 2.53/2.73      (![X0 : $i]:
% 2.53/2.73         (~ (v1_xboole_0 @ X0)
% 2.53/2.73          | ((k4_relat_1 @ X0) = (k1_xboole_0))
% 2.53/2.73          | ~ (v1_relat_1 @ X0))),
% 2.53/2.73      inference('sup-', [status(thm)], ['54', '74'])).
% 2.53/2.73  thf(cc1_relat_1, axiom,
% 2.53/2.73    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 2.53/2.73  thf('76', plain, (![X55 : $i]: ((v1_relat_1 @ X55) | ~ (v1_xboole_0 @ X55))),
% 2.53/2.73      inference('cnf', [status(esa)], [cc1_relat_1])).
% 2.53/2.73  thf('77', plain,
% 2.53/2.73      (![X0 : $i]: (((k4_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.53/2.73      inference('clc', [status(thm)], ['75', '76'])).
% 2.53/2.73  thf('78', plain,
% 2.53/2.73      (![X65 : $i]:
% 2.53/2.73         (((k2_relat_1 @ X65) = (k1_relat_1 @ (k4_relat_1 @ X65)))
% 2.53/2.73          | ~ (v1_relat_1 @ X65))),
% 2.53/2.73      inference('cnf', [status(esa)], [t37_relat_1])).
% 2.53/2.73  thf('79', plain,
% 2.53/2.73      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 2.53/2.73      inference('sup-', [status(thm)], ['20', '21'])).
% 2.53/2.73  thf('80', plain,
% 2.53/2.73      (![X0 : $i]:
% 2.53/2.73         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 2.53/2.73          | ~ (v1_relat_1 @ X0)
% 2.53/2.73          | ~ (v1_xboole_0 @ (k4_relat_1 @ X0)))),
% 2.53/2.73      inference('sup+', [status(thm)], ['78', '79'])).
% 2.53/2.73  thf('81', plain,
% 2.53/2.73      (![X0 : $i]:
% 2.53/2.73         (~ (v1_xboole_0 @ k1_xboole_0)
% 2.53/2.73          | ~ (v1_xboole_0 @ X0)
% 2.53/2.73          | ~ (v1_relat_1 @ X0)
% 2.53/2.73          | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 2.53/2.73      inference('sup-', [status(thm)], ['77', '80'])).
% 2.53/2.73  thf('82', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.53/2.73      inference('demod', [status(thm)], ['40', '43'])).
% 2.53/2.73  thf('83', plain,
% 2.53/2.73      (![X0 : $i]:
% 2.53/2.73         (~ (v1_xboole_0 @ X0)
% 2.53/2.73          | ~ (v1_relat_1 @ X0)
% 2.53/2.73          | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 2.53/2.73      inference('demod', [status(thm)], ['81', '82'])).
% 2.53/2.73  thf('84', plain, (![X55 : $i]: ((v1_relat_1 @ X55) | ~ (v1_xboole_0 @ X55))),
% 2.53/2.73      inference('cnf', [status(esa)], [cc1_relat_1])).
% 2.53/2.73  thf('85', plain,
% 2.53/2.73      (![X0 : $i]: (((k2_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.53/2.73      inference('clc', [status(thm)], ['83', '84'])).
% 2.53/2.73  thf('86', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.53/2.73      inference('sup-', [status(thm)], ['53', '85'])).
% 2.53/2.73  thf('87', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.53/2.73      inference('demod', [status(thm)], ['40', '43'])).
% 2.53/2.73  thf('88', plain, ($false),
% 2.53/2.73      inference('demod', [status(thm)], ['52', '86', '87'])).
% 2.53/2.73  
% 2.53/2.73  % SZS output end Refutation
% 2.53/2.73  
% 2.53/2.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
