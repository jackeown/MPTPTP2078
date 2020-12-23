%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DROv8rpWIC

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:43 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.72s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 228 expanded)
%              Number of leaves         :   29 (  83 expanded)
%              Depth                    :   23
%              Number of atoms          :  715 (1470 expanded)
%              Number of equality atoms :   67 ( 122 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( v1_relat_1 @ X39 )
      | ~ ( v1_relat_1 @ X40 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X39 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X38: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X38 ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('3',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( v1_relat_1 @ X39 )
      | ~ ( v1_relat_1 @ X40 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X39 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('4',plain,
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

thf('5',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( v1_relat_1 @ X44 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X45 @ X44 ) )
        = ( k1_relat_1 @ X45 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X45 ) @ ( k1_relat_1 @ X44 ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('7',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('8',plain,(
    ! [X35: $i] :
      ( ( v1_relat_1 @ X35 )
      | ( r2_hidden @ ( sk_B @ X35 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('9',plain,(
    ! [X2: $i] :
      ( r1_xboole_0 @ X2 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t55_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        & ( r2_hidden @ A @ C ) ) )).

thf('10',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X30 @ X31 ) @ X32 )
      | ~ ( r2_hidden @ X30 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('11',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7','12','13'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X41: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X41 ) )
      | ~ ( v1_relat_1 @ X41 )
      | ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('17',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','18'])).

thf('20',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','11'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','25'])).

thf('27',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('28',plain,(
    ! [X38: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X38 ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('29',plain,(
    ! [X43: $i] :
      ( ( ( k2_relat_1 @ X43 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X43 ) ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('30',plain,(
    ! [X41: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X41 ) )
      | ~ ( v1_relat_1 @ X41 )
      | ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k4_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','33'])).

thf('35',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('36',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','11'])).

thf('37',plain,(
    v1_xboole_0 @ ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('39',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('40',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( v1_relat_1 @ X46 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X47 @ X46 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X46 ) @ ( k4_relat_1 @ X47 ) ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k5_relat_1 @ k1_xboole_0 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','11'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k5_relat_1 @ k1_xboole_0 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','43'])).

thf('45',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf(involutiveness_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) )
        = A ) ) )).

thf('48',plain,(
    ! [X42: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X42 ) )
        = X42 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ k1_xboole_0 )
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','51'])).

thf('53',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','11'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

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

thf('57',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['57'])).

thf('59',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('65',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['57'])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('70',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('74',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['57'])).

thf('76',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['59','76'])).

thf('78',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('81',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    $false ),
    inference(simplify,[status(thm)],['81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DROv8rpWIC
% 0.13/0.38  % Computer   : n016.cluster.edu
% 0.13/0.38  % Model      : x86_64 x86_64
% 0.13/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.38  % Memory     : 8042.1875MB
% 0.13/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.38  % CPULimit   : 60
% 0.13/0.38  % DateTime   : Tue Dec  1 17:00:19 EST 2020
% 0.13/0.38  % CPUTime    : 
% 0.13/0.38  % Running portfolio for 600 s
% 0.13/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.38  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.67/0.89  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.67/0.89  % Solved by: fo/fo7.sh
% 0.67/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.67/0.89  % done 926 iterations in 0.411s
% 0.67/0.89  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.67/0.89  % SZS output start Refutation
% 0.67/0.89  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.67/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.67/0.89  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.67/0.89  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.67/0.89  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.67/0.89  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.67/0.89  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.67/0.89  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.67/0.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.67/0.89  thf(sk_B_type, type, sk_B: $i > $i).
% 0.67/0.89  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.67/0.89  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.67/0.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.67/0.89  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.67/0.89  thf(dt_k5_relat_1, axiom,
% 0.67/0.89    (![A:$i,B:$i]:
% 0.67/0.89     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.67/0.89       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.67/0.89  thf('0', plain,
% 0.67/0.89      (![X39 : $i, X40 : $i]:
% 0.67/0.89         (~ (v1_relat_1 @ X39)
% 0.67/0.89          | ~ (v1_relat_1 @ X40)
% 0.67/0.89          | (v1_relat_1 @ (k5_relat_1 @ X39 @ X40)))),
% 0.67/0.89      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.67/0.89  thf(dt_k4_relat_1, axiom,
% 0.67/0.89    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.67/0.89  thf('1', plain,
% 0.67/0.89      (![X38 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X38)) | ~ (v1_relat_1 @ X38))),
% 0.67/0.89      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.67/0.89  thf(l13_xboole_0, axiom,
% 0.67/0.89    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.67/0.89  thf('2', plain,
% 0.67/0.89      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.67/0.89      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.67/0.89  thf('3', plain,
% 0.67/0.89      (![X39 : $i, X40 : $i]:
% 0.67/0.89         (~ (v1_relat_1 @ X39)
% 0.67/0.89          | ~ (v1_relat_1 @ X40)
% 0.67/0.89          | (v1_relat_1 @ (k5_relat_1 @ X39 @ X40)))),
% 0.67/0.89      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.67/0.89  thf(t60_relat_1, axiom,
% 0.67/0.89    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.67/0.89     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.67/0.89  thf('4', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.67/0.89      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.67/0.89  thf(t46_relat_1, axiom,
% 0.67/0.89    (![A:$i]:
% 0.67/0.89     ( ( v1_relat_1 @ A ) =>
% 0.67/0.89       ( ![B:$i]:
% 0.67/0.89         ( ( v1_relat_1 @ B ) =>
% 0.67/0.89           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.67/0.89             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.67/0.89  thf('5', plain,
% 0.67/0.89      (![X44 : $i, X45 : $i]:
% 0.67/0.89         (~ (v1_relat_1 @ X44)
% 0.67/0.89          | ((k1_relat_1 @ (k5_relat_1 @ X45 @ X44)) = (k1_relat_1 @ X45))
% 0.67/0.89          | ~ (r1_tarski @ (k2_relat_1 @ X45) @ (k1_relat_1 @ X44))
% 0.67/0.89          | ~ (v1_relat_1 @ X45))),
% 0.67/0.89      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.67/0.89  thf('6', plain,
% 0.67/0.89      (![X0 : $i]:
% 0.67/0.89         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.67/0.89          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.67/0.89          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.67/0.89              = (k1_relat_1 @ k1_xboole_0))
% 0.67/0.89          | ~ (v1_relat_1 @ X0))),
% 0.67/0.89      inference('sup-', [status(thm)], ['4', '5'])).
% 0.67/0.89  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.67/0.89  thf('7', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.67/0.89      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.67/0.89  thf(d1_relat_1, axiom,
% 0.67/0.89    (![A:$i]:
% 0.67/0.89     ( ( v1_relat_1 @ A ) <=>
% 0.67/0.89       ( ![B:$i]:
% 0.67/0.89         ( ~( ( r2_hidden @ B @ A ) & 
% 0.67/0.89              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.67/0.89  thf('8', plain,
% 0.67/0.89      (![X35 : $i]: ((v1_relat_1 @ X35) | (r2_hidden @ (sk_B @ X35) @ X35))),
% 0.67/0.89      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.67/0.89  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.67/0.89  thf('9', plain, (![X2 : $i]: (r1_xboole_0 @ X2 @ k1_xboole_0)),
% 0.67/0.89      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.67/0.89  thf(t55_zfmisc_1, axiom,
% 0.67/0.89    (![A:$i,B:$i,C:$i]:
% 0.67/0.89     ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & ( r2_hidden @ A @ C ) ) ))).
% 0.67/0.89  thf('10', plain,
% 0.67/0.89      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.67/0.89         (~ (r1_xboole_0 @ (k2_tarski @ X30 @ X31) @ X32)
% 0.67/0.89          | ~ (r2_hidden @ X30 @ X32))),
% 0.67/0.89      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 0.67/0.89  thf('11', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.67/0.89      inference('sup-', [status(thm)], ['9', '10'])).
% 0.67/0.89  thf('12', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.67/0.89      inference('sup-', [status(thm)], ['8', '11'])).
% 0.67/0.89  thf('13', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.67/0.89      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.67/0.89  thf('14', plain,
% 0.67/0.89      (![X0 : $i]:
% 0.67/0.89         (((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.67/0.89          | ~ (v1_relat_1 @ X0))),
% 0.67/0.89      inference('demod', [status(thm)], ['6', '7', '12', '13'])).
% 0.67/0.89  thf(fc8_relat_1, axiom,
% 0.67/0.89    (![A:$i]:
% 0.67/0.89     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.67/0.89       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.67/0.89  thf('15', plain,
% 0.67/0.89      (![X41 : $i]:
% 0.67/0.89         (~ (v1_xboole_0 @ (k1_relat_1 @ X41))
% 0.67/0.89          | ~ (v1_relat_1 @ X41)
% 0.67/0.89          | (v1_xboole_0 @ X41))),
% 0.67/0.89      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.67/0.89  thf('16', plain,
% 0.67/0.89      (![X0 : $i]:
% 0.67/0.89         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.67/0.89          | ~ (v1_relat_1 @ X0)
% 0.67/0.89          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.67/0.89          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.67/0.89      inference('sup-', [status(thm)], ['14', '15'])).
% 0.67/0.89  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.67/0.89  thf('17', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.67/0.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.67/0.89  thf('18', plain,
% 0.67/0.89      (![X0 : $i]:
% 0.67/0.89         (~ (v1_relat_1 @ X0)
% 0.67/0.89          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.67/0.89          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.67/0.89      inference('demod', [status(thm)], ['16', '17'])).
% 0.67/0.89  thf('19', plain,
% 0.67/0.89      (![X0 : $i]:
% 0.67/0.89         (~ (v1_relat_1 @ X0)
% 0.67/0.89          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.67/0.89          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.67/0.89          | ~ (v1_relat_1 @ X0))),
% 0.67/0.89      inference('sup-', [status(thm)], ['3', '18'])).
% 0.67/0.89  thf('20', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.67/0.89      inference('sup-', [status(thm)], ['8', '11'])).
% 0.67/0.89  thf('21', plain,
% 0.67/0.89      (![X0 : $i]:
% 0.67/0.89         (~ (v1_relat_1 @ X0)
% 0.67/0.89          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.67/0.89          | ~ (v1_relat_1 @ X0))),
% 0.67/0.89      inference('demod', [status(thm)], ['19', '20'])).
% 0.67/0.89  thf('22', plain,
% 0.67/0.89      (![X0 : $i]:
% 0.67/0.89         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.67/0.89      inference('simplify', [status(thm)], ['21'])).
% 0.67/0.89  thf('23', plain,
% 0.67/0.89      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.67/0.89      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.67/0.89  thf('24', plain,
% 0.67/0.89      (![X0 : $i]:
% 0.67/0.89         (~ (v1_relat_1 @ X0)
% 0.67/0.89          | ((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.67/0.89      inference('sup-', [status(thm)], ['22', '23'])).
% 0.67/0.89  thf('25', plain,
% 0.67/0.89      (![X0 : $i, X1 : $i]:
% 0.67/0.89         (((k5_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.67/0.89          | ~ (v1_xboole_0 @ X0)
% 0.67/0.89          | ~ (v1_relat_1 @ X1))),
% 0.67/0.89      inference('sup+', [status(thm)], ['2', '24'])).
% 0.67/0.89  thf('26', plain,
% 0.67/0.89      (![X0 : $i, X1 : $i]:
% 0.67/0.89         (~ (v1_relat_1 @ X0)
% 0.67/0.89          | ~ (v1_xboole_0 @ X1)
% 0.67/0.89          | ((k5_relat_1 @ X1 @ (k4_relat_1 @ X0)) = (k1_xboole_0)))),
% 0.67/0.89      inference('sup-', [status(thm)], ['1', '25'])).
% 0.67/0.89  thf('27', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.67/0.89      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.67/0.89  thf('28', plain,
% 0.67/0.89      (![X38 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X38)) | ~ (v1_relat_1 @ X38))),
% 0.67/0.89      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.67/0.89  thf(t37_relat_1, axiom,
% 0.67/0.89    (![A:$i]:
% 0.67/0.89     ( ( v1_relat_1 @ A ) =>
% 0.67/0.89       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.67/0.89         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.67/0.89  thf('29', plain,
% 0.67/0.89      (![X43 : $i]:
% 0.67/0.89         (((k2_relat_1 @ X43) = (k1_relat_1 @ (k4_relat_1 @ X43)))
% 0.67/0.89          | ~ (v1_relat_1 @ X43))),
% 0.67/0.89      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.67/0.89  thf('30', plain,
% 0.67/0.89      (![X41 : $i]:
% 0.67/0.89         (~ (v1_xboole_0 @ (k1_relat_1 @ X41))
% 0.67/0.89          | ~ (v1_relat_1 @ X41)
% 0.67/0.89          | (v1_xboole_0 @ X41))),
% 0.67/0.89      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.67/0.89  thf('31', plain,
% 0.67/0.89      (![X0 : $i]:
% 0.67/0.89         (~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.67/0.89          | ~ (v1_relat_1 @ X0)
% 0.67/0.90          | (v1_xboole_0 @ (k4_relat_1 @ X0))
% 0.67/0.90          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.67/0.90      inference('sup-', [status(thm)], ['29', '30'])).
% 0.67/0.90  thf('32', plain,
% 0.67/0.90      (![X0 : $i]:
% 0.67/0.90         (~ (v1_relat_1 @ X0)
% 0.67/0.90          | (v1_xboole_0 @ (k4_relat_1 @ X0))
% 0.67/0.90          | ~ (v1_relat_1 @ X0)
% 0.67/0.90          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0)))),
% 0.67/0.90      inference('sup-', [status(thm)], ['28', '31'])).
% 0.67/0.90  thf('33', plain,
% 0.67/0.90      (![X0 : $i]:
% 0.67/0.90         (~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.67/0.90          | (v1_xboole_0 @ (k4_relat_1 @ X0))
% 0.67/0.90          | ~ (v1_relat_1 @ X0))),
% 0.67/0.90      inference('simplify', [status(thm)], ['32'])).
% 0.67/0.90  thf('34', plain,
% 0.67/0.90      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.67/0.90        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.67/0.90        | (v1_xboole_0 @ (k4_relat_1 @ k1_xboole_0)))),
% 0.67/0.90      inference('sup-', [status(thm)], ['27', '33'])).
% 0.67/0.90  thf('35', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.67/0.90      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.67/0.90  thf('36', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.67/0.90      inference('sup-', [status(thm)], ['8', '11'])).
% 0.67/0.90  thf('37', plain, ((v1_xboole_0 @ (k4_relat_1 @ k1_xboole_0))),
% 0.67/0.90      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.67/0.90  thf('38', plain,
% 0.67/0.90      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.67/0.90      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.67/0.90  thf('39', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.67/0.90      inference('sup-', [status(thm)], ['37', '38'])).
% 0.67/0.90  thf(t54_relat_1, axiom,
% 0.67/0.90    (![A:$i]:
% 0.67/0.90     ( ( v1_relat_1 @ A ) =>
% 0.67/0.90       ( ![B:$i]:
% 0.67/0.90         ( ( v1_relat_1 @ B ) =>
% 0.67/0.90           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.67/0.90             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 0.67/0.90  thf('40', plain,
% 0.67/0.90      (![X46 : $i, X47 : $i]:
% 0.67/0.90         (~ (v1_relat_1 @ X46)
% 0.67/0.90          | ((k4_relat_1 @ (k5_relat_1 @ X47 @ X46))
% 0.67/0.90              = (k5_relat_1 @ (k4_relat_1 @ X46) @ (k4_relat_1 @ X47)))
% 0.67/0.90          | ~ (v1_relat_1 @ X47))),
% 0.67/0.90      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.67/0.90  thf('41', plain,
% 0.67/0.90      (![X0 : $i]:
% 0.67/0.90         (((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.67/0.90            = (k5_relat_1 @ k1_xboole_0 @ (k4_relat_1 @ X0)))
% 0.67/0.90          | ~ (v1_relat_1 @ X0)
% 0.67/0.90          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.67/0.90      inference('sup+', [status(thm)], ['39', '40'])).
% 0.67/0.90  thf('42', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.67/0.90      inference('sup-', [status(thm)], ['8', '11'])).
% 0.67/0.90  thf('43', plain,
% 0.67/0.90      (![X0 : $i]:
% 0.67/0.90         (((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.67/0.90            = (k5_relat_1 @ k1_xboole_0 @ (k4_relat_1 @ X0)))
% 0.67/0.90          | ~ (v1_relat_1 @ X0))),
% 0.67/0.90      inference('demod', [status(thm)], ['41', '42'])).
% 0.67/0.90  thf('44', plain,
% 0.67/0.90      (![X0 : $i]:
% 0.67/0.90         (((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))
% 0.67/0.90          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.67/0.90          | ~ (v1_relat_1 @ X0)
% 0.67/0.90          | ~ (v1_relat_1 @ X0))),
% 0.67/0.90      inference('sup+', [status(thm)], ['26', '43'])).
% 0.67/0.90  thf('45', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.67/0.90      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.67/0.90  thf('46', plain,
% 0.67/0.90      (![X0 : $i]:
% 0.67/0.90         (((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))
% 0.67/0.90          | ~ (v1_relat_1 @ X0)
% 0.67/0.90          | ~ (v1_relat_1 @ X0))),
% 0.67/0.90      inference('demod', [status(thm)], ['44', '45'])).
% 0.67/0.90  thf('47', plain,
% 0.67/0.90      (![X0 : $i]:
% 0.67/0.90         (~ (v1_relat_1 @ X0)
% 0.67/0.90          | ((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.67/0.90      inference('simplify', [status(thm)], ['46'])).
% 0.67/0.90  thf(involutiveness_k4_relat_1, axiom,
% 0.67/0.90    (![A:$i]:
% 0.67/0.90     ( ( v1_relat_1 @ A ) => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) ) = ( A ) ) ))).
% 0.67/0.90  thf('48', plain,
% 0.67/0.90      (![X42 : $i]:
% 0.67/0.90         (((k4_relat_1 @ (k4_relat_1 @ X42)) = (X42)) | ~ (v1_relat_1 @ X42))),
% 0.67/0.90      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 0.67/0.90  thf('49', plain,
% 0.67/0.90      (![X0 : $i]:
% 0.67/0.90         (((k4_relat_1 @ k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.67/0.90          | ~ (v1_relat_1 @ X0)
% 0.67/0.90          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.67/0.90      inference('sup+', [status(thm)], ['47', '48'])).
% 0.67/0.90  thf('50', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.67/0.90      inference('sup-', [status(thm)], ['37', '38'])).
% 0.67/0.90  thf('51', plain,
% 0.67/0.90      (![X0 : $i]:
% 0.67/0.90         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.67/0.90          | ~ (v1_relat_1 @ X0)
% 0.67/0.90          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.67/0.90      inference('demod', [status(thm)], ['49', '50'])).
% 0.67/0.90  thf('52', plain,
% 0.67/0.90      (![X0 : $i]:
% 0.67/0.90         (~ (v1_relat_1 @ k1_xboole_0)
% 0.67/0.90          | ~ (v1_relat_1 @ X0)
% 0.67/0.90          | ~ (v1_relat_1 @ X0)
% 0.67/0.90          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.67/0.90      inference('sup-', [status(thm)], ['0', '51'])).
% 0.67/0.90  thf('53', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.67/0.90      inference('sup-', [status(thm)], ['8', '11'])).
% 0.67/0.90  thf('54', plain,
% 0.67/0.90      (![X0 : $i]:
% 0.67/0.90         (~ (v1_relat_1 @ X0)
% 0.67/0.90          | ~ (v1_relat_1 @ X0)
% 0.67/0.90          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.67/0.90      inference('demod', [status(thm)], ['52', '53'])).
% 0.67/0.90  thf('55', plain,
% 0.67/0.90      (![X0 : $i]:
% 0.67/0.90         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.67/0.90          | ~ (v1_relat_1 @ X0))),
% 0.67/0.90      inference('simplify', [status(thm)], ['54'])).
% 0.67/0.90  thf('56', plain,
% 0.67/0.90      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.67/0.90      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.67/0.90  thf(t62_relat_1, conjecture,
% 0.67/0.90    (![A:$i]:
% 0.67/0.90     ( ( v1_relat_1 @ A ) =>
% 0.67/0.90       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.67/0.90         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.67/0.90  thf(zf_stmt_0, negated_conjecture,
% 0.67/0.90    (~( ![A:$i]:
% 0.67/0.90        ( ( v1_relat_1 @ A ) =>
% 0.67/0.90          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.67/0.90            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.67/0.90    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.67/0.90  thf('57', plain,
% 0.67/0.90      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.67/0.90        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('58', plain,
% 0.67/0.90      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.67/0.90         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.67/0.90      inference('split', [status(esa)], ['57'])).
% 0.67/0.90  thf('59', plain,
% 0.67/0.90      ((![X0 : $i]:
% 0.67/0.90          (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.67/0.90         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.67/0.90      inference('sup-', [status(thm)], ['56', '58'])).
% 0.67/0.90  thf('60', plain,
% 0.67/0.90      (![X0 : $i]:
% 0.67/0.90         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.67/0.90      inference('simplify', [status(thm)], ['21'])).
% 0.67/0.90  thf('61', plain,
% 0.67/0.90      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.67/0.90      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.67/0.90  thf('62', plain,
% 0.67/0.90      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.67/0.90      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.67/0.90  thf('63', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]:
% 0.67/0.90         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.67/0.90      inference('sup+', [status(thm)], ['61', '62'])).
% 0.67/0.90  thf('64', plain,
% 0.67/0.90      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.67/0.90      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.67/0.90  thf('65', plain,
% 0.67/0.90      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.67/0.90         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.90      inference('split', [status(esa)], ['57'])).
% 0.67/0.90  thf('66', plain,
% 0.67/0.90      ((![X0 : $i]:
% 0.67/0.90          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.67/0.90         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.90      inference('sup-', [status(thm)], ['64', '65'])).
% 0.67/0.90  thf('67', plain,
% 0.67/0.90      ((![X0 : $i, X1 : $i]:
% 0.67/0.90          (((X0) != (k1_xboole_0))
% 0.67/0.90           | ~ (v1_xboole_0 @ X0)
% 0.67/0.90           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.67/0.90           | ~ (v1_xboole_0 @ X1)))
% 0.67/0.90         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.90      inference('sup-', [status(thm)], ['63', '66'])).
% 0.67/0.90  thf('68', plain,
% 0.67/0.90      ((![X1 : $i]:
% 0.67/0.90          (~ (v1_xboole_0 @ X1)
% 0.67/0.90           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.67/0.90           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.67/0.90         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.90      inference('simplify', [status(thm)], ['67'])).
% 0.67/0.90  thf('69', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.67/0.90      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.67/0.90  thf('70', plain,
% 0.67/0.90      ((![X1 : $i]:
% 0.67/0.90          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))))
% 0.67/0.90         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.90      inference('simplify_reflect+', [status(thm)], ['68', '69'])).
% 0.67/0.90  thf('71', plain,
% 0.67/0.90      (((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.67/0.90         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.67/0.90      inference('sup-', [status(thm)], ['60', '70'])).
% 0.67/0.90  thf('72', plain, ((v1_relat_1 @ sk_A)),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('73', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.67/0.90      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.67/0.90  thf('74', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.67/0.90      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.67/0.90  thf('75', plain,
% 0.67/0.90      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.67/0.90       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.67/0.90      inference('split', [status(esa)], ['57'])).
% 0.67/0.90  thf('76', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.67/0.90      inference('sat_resolution*', [status(thm)], ['74', '75'])).
% 0.67/0.90  thf('77', plain,
% 0.67/0.90      (![X0 : $i]:
% 0.67/0.90         (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.72/0.90      inference('simpl_trail', [status(thm)], ['59', '76'])).
% 0.72/0.90  thf('78', plain,
% 0.72/0.90      ((((k1_xboole_0) != (k1_xboole_0))
% 0.72/0.90        | ~ (v1_relat_1 @ sk_A)
% 0.72/0.90        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.72/0.90      inference('sup-', [status(thm)], ['55', '77'])).
% 0.72/0.90  thf('79', plain, ((v1_relat_1 @ sk_A)),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('80', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.72/0.90      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.72/0.90  thf('81', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.72/0.90      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.72/0.90  thf('82', plain, ($false), inference('simplify', [status(thm)], ['81'])).
% 0.72/0.90  
% 0.72/0.90  % SZS output end Refutation
% 0.72/0.90  
% 0.72/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
