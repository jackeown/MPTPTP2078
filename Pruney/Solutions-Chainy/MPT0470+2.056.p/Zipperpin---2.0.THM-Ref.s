%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.azJuKmJd93

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:34 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 227 expanded)
%              Number of leaves         :   32 (  84 expanded)
%              Depth                    :   20
%              Number of atoms          :  947 (1580 expanded)
%              Number of equality atoms :   96 ( 164 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('0',plain,(
    ! [X47: $i] :
      ( ( v1_relat_1 @ X47 )
      | ~ ( v1_xboole_0 @ X47 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( v1_relat_1 @ X48 )
      | ~ ( v1_relat_1 @ X49 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X48 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('2',plain,(
    ! [X47: $i] :
      ( ( v1_relat_1 @ X47 )
      | ~ ( v1_xboole_0 @ X47 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('3',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t47_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( v1_relat_1 @ X53 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X53 @ X54 ) )
        = ( k2_relat_1 @ X54 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X54 ) @ ( k2_relat_1 @ X53 ) )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('6',plain,(
    ! [X12: $i] :
      ( r1_tarski @ k1_xboole_0 @ X12 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('7',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('10',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t22_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('12',plain,(
    ! [X50: $i] :
      ( ( ( k3_xboole_0 @ X50 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X50 ) ) )
        = X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X45 @ X46 ) )
      = ( k3_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('14',plain,(
    ! [X50: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X50 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X50 ) ) ) )
        = X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) )
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('16',plain,(
    ! [X13: $i] :
      ( r1_xboole_0 @ X13 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t127_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ A @ B )
        | ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('17',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X41 @ X42 ) @ ( k2_zfmisc_1 @ X43 @ X44 ) )
      | ~ ( r1_xboole_0 @ X42 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('19',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('20',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('21',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X45 @ X46 ) )
      = ( k3_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('22',plain,(
    ! [X3: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X3 @ X3 ) )
      = X3 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('23',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ X7 @ X10 ) )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('24',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X45 @ X46 ) )
      = ( k3_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('25',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k1_setfam_1 @ ( k2_tarski @ X7 @ X10 ) ) )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','27'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('29',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('31',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('32',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X45 @ X46 ) )
      = ( k3_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('33',plain,(
    ! [X11: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X11 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['15','30','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['1','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','36'])).

thf('38',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('41',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('46',plain,(
    ! [X13: $i] :
      ( r1_xboole_0 @ X13 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('47',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X41 @ X42 ) @ ( k2_zfmisc_1 @ X43 @ X44 ) )
      | ~ ( r1_xboole_0 @ X41 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X2 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','26'])).

thf('50',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','52'])).

thf('54',plain,(
    ! [X50: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X50 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X50 ) ) ) )
        = X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('55',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('56',plain,(
    ! [X11: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X11 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

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

thf('58',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['58'])).

thf('60',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( k5_relat_1 @ sk_A @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','60'])).

thf('62',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
        | ~ ( v1_relat_1 @ X0 )
        | ( ( k5_relat_1 @ sk_A @ X0 )
         != k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','61'])).

thf('63',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('64',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
        | ~ ( v1_relat_1 @ X0 )
        | ( ( k5_relat_1 @ sk_A @ X0 )
         != k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ X0 )
        | ( ( k5_relat_1 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','64'])).

thf('66',plain,(
    ! [X47: $i] :
      ( ( v1_relat_1 @ X47 )
      | ~ ( v1_xboole_0 @ X47 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('67',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( v1_relat_1 @ X48 )
      | ~ ( v1_relat_1 @ X49 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X48 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('68',plain,(
    ! [X47: $i] :
      ( ( v1_relat_1 @ X47 )
      | ~ ( v1_xboole_0 @ X47 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('69',plain,
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

thf('70',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( v1_relat_1 @ X51 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X52 @ X51 ) )
        = ( k1_relat_1 @ X52 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X52 ) @ ( k1_relat_1 @ X51 ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X12: $i] :
      ( r1_tarski @ k1_xboole_0 @ X12 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('73',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['68','74'])).

thf('76',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X50: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X50 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X50 ) ) ) )
        = X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ) )
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('81',plain,(
    ! [X11: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X11 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['66','84'])).

thf('86',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('89',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['58'])).

thf('90',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['87','90'])).

thf('92',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('94',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['58'])).

thf('97',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k5_relat_1 @ sk_A @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['65','97'])).

thf('99',plain,(
    ! [X47: $i] :
      ( ( v1_relat_1 @ X47 )
      | ~ ( v1_xboole_0 @ X47 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','100'])).

thf('102',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('104',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,(
    $false ),
    inference(simplify,[status(thm)],['104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.azJuKmJd93
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:58:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.48/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.48/0.70  % Solved by: fo/fo7.sh
% 0.48/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.70  % done 302 iterations in 0.245s
% 0.48/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.48/0.70  % SZS output start Refutation
% 0.48/0.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.48/0.70  thf(sk_B_type, type, sk_B: $i > $i).
% 0.48/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.48/0.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.48/0.70  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.48/0.70  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.48/0.70  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.48/0.70  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.48/0.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.48/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.48/0.70  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.48/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.48/0.70  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.48/0.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.48/0.70  thf(cc1_relat_1, axiom,
% 0.48/0.70    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.48/0.70  thf('0', plain, (![X47 : $i]: ((v1_relat_1 @ X47) | ~ (v1_xboole_0 @ X47))),
% 0.48/0.70      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.48/0.70  thf(dt_k5_relat_1, axiom,
% 0.48/0.70    (![A:$i,B:$i]:
% 0.48/0.70     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.48/0.70       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.48/0.70  thf('1', plain,
% 0.48/0.70      (![X48 : $i, X49 : $i]:
% 0.48/0.70         (~ (v1_relat_1 @ X48)
% 0.48/0.70          | ~ (v1_relat_1 @ X49)
% 0.48/0.70          | (v1_relat_1 @ (k5_relat_1 @ X48 @ X49)))),
% 0.48/0.70      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.48/0.70  thf('2', plain, (![X47 : $i]: ((v1_relat_1 @ X47) | ~ (v1_xboole_0 @ X47))),
% 0.48/0.70      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.48/0.70  thf(t60_relat_1, axiom,
% 0.48/0.70    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.48/0.70     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.48/0.70  thf('3', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.48/0.70      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.48/0.70  thf(t47_relat_1, axiom,
% 0.48/0.70    (![A:$i]:
% 0.48/0.70     ( ( v1_relat_1 @ A ) =>
% 0.48/0.70       ( ![B:$i]:
% 0.48/0.70         ( ( v1_relat_1 @ B ) =>
% 0.48/0.70           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.48/0.70             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.48/0.70  thf('4', plain,
% 0.48/0.70      (![X53 : $i, X54 : $i]:
% 0.48/0.70         (~ (v1_relat_1 @ X53)
% 0.48/0.70          | ((k2_relat_1 @ (k5_relat_1 @ X53 @ X54)) = (k2_relat_1 @ X54))
% 0.48/0.70          | ~ (r1_tarski @ (k1_relat_1 @ X54) @ (k2_relat_1 @ X53))
% 0.48/0.70          | ~ (v1_relat_1 @ X54))),
% 0.48/0.70      inference('cnf', [status(esa)], [t47_relat_1])).
% 0.48/0.70  thf('5', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (r1_tarski @ k1_xboole_0 @ (k2_relat_1 @ X0))
% 0.48/0.70          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.48/0.70          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.48/0.70              = (k2_relat_1 @ k1_xboole_0))
% 0.48/0.70          | ~ (v1_relat_1 @ X0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['3', '4'])).
% 0.48/0.70  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.48/0.70  thf('6', plain, (![X12 : $i]: (r1_tarski @ k1_xboole_0 @ X12)),
% 0.48/0.70      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.48/0.70  thf('7', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.48/0.70      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.48/0.70  thf('8', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (v1_relat_1 @ k1_xboole_0)
% 0.48/0.70          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))
% 0.48/0.70          | ~ (v1_relat_1 @ X0))),
% 0.48/0.70      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.48/0.70  thf('9', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.48/0.70          | ~ (v1_relat_1 @ X0)
% 0.48/0.70          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.48/0.70      inference('sup-', [status(thm)], ['2', '8'])).
% 0.48/0.70  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.48/0.70  thf('10', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.48/0.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.48/0.70  thf('11', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (v1_relat_1 @ X0)
% 0.48/0.70          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.48/0.70      inference('demod', [status(thm)], ['9', '10'])).
% 0.48/0.70  thf(t22_relat_1, axiom,
% 0.48/0.70    (![A:$i]:
% 0.48/0.70     ( ( v1_relat_1 @ A ) =>
% 0.48/0.70       ( ( k3_xboole_0 @
% 0.48/0.70           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 0.48/0.70         ( A ) ) ))).
% 0.48/0.70  thf('12', plain,
% 0.48/0.70      (![X50 : $i]:
% 0.48/0.70         (((k3_xboole_0 @ X50 @ 
% 0.48/0.70            (k2_zfmisc_1 @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X50))) = (
% 0.48/0.70            X50))
% 0.48/0.70          | ~ (v1_relat_1 @ X50))),
% 0.48/0.70      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.48/0.70  thf(t12_setfam_1, axiom,
% 0.48/0.70    (![A:$i,B:$i]:
% 0.48/0.70     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.48/0.70  thf('13', plain,
% 0.48/0.70      (![X45 : $i, X46 : $i]:
% 0.48/0.70         ((k1_setfam_1 @ (k2_tarski @ X45 @ X46)) = (k3_xboole_0 @ X45 @ X46))),
% 0.48/0.70      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.48/0.70  thf('14', plain,
% 0.48/0.70      (![X50 : $i]:
% 0.48/0.70         (((k1_setfam_1 @ 
% 0.48/0.70            (k2_tarski @ X50 @ 
% 0.48/0.70             (k2_zfmisc_1 @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X50))))
% 0.48/0.70            = (X50))
% 0.48/0.70          | ~ (v1_relat_1 @ X50))),
% 0.48/0.70      inference('demod', [status(thm)], ['12', '13'])).
% 0.48/0.70  thf('15', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (((k1_setfam_1 @ 
% 0.48/0.70            (k2_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ 
% 0.48/0.70             (k2_zfmisc_1 @ (k1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.48/0.70              k1_xboole_0)))
% 0.48/0.70            = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.48/0.70          | ~ (v1_relat_1 @ X0)
% 0.48/0.70          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.48/0.70      inference('sup+', [status(thm)], ['11', '14'])).
% 0.48/0.70  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.48/0.70  thf('16', plain, (![X13 : $i]: (r1_xboole_0 @ X13 @ k1_xboole_0)),
% 0.48/0.70      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.48/0.70  thf(t127_zfmisc_1, axiom,
% 0.48/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.70     ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 0.48/0.70       ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.48/0.70  thf('17', plain,
% 0.48/0.70      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.48/0.70         ((r1_xboole_0 @ (k2_zfmisc_1 @ X41 @ X42) @ (k2_zfmisc_1 @ X43 @ X44))
% 0.48/0.70          | ~ (r1_xboole_0 @ X42 @ X44))),
% 0.48/0.70      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.48/0.70  thf('18', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.70         (r1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ 
% 0.48/0.70          (k2_zfmisc_1 @ X1 @ k1_xboole_0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['16', '17'])).
% 0.48/0.70  thf(d1_xboole_0, axiom,
% 0.48/0.70    (![A:$i]:
% 0.48/0.70     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.48/0.70  thf('19', plain,
% 0.48/0.70      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.48/0.70      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.48/0.70  thf(idempotence_k3_xboole_0, axiom,
% 0.48/0.70    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.48/0.70  thf('20', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.48/0.70      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.48/0.70  thf('21', plain,
% 0.48/0.70      (![X45 : $i, X46 : $i]:
% 0.48/0.70         ((k1_setfam_1 @ (k2_tarski @ X45 @ X46)) = (k3_xboole_0 @ X45 @ X46))),
% 0.48/0.70      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.48/0.70  thf('22', plain,
% 0.48/0.70      (![X3 : $i]: ((k1_setfam_1 @ (k2_tarski @ X3 @ X3)) = (X3))),
% 0.48/0.70      inference('demod', [status(thm)], ['20', '21'])).
% 0.48/0.70  thf(t4_xboole_0, axiom,
% 0.48/0.70    (![A:$i,B:$i]:
% 0.48/0.70     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.48/0.70            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.48/0.70       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.48/0.70            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.48/0.70  thf('23', plain,
% 0.48/0.70      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.48/0.70         (~ (r2_hidden @ X9 @ (k3_xboole_0 @ X7 @ X10))
% 0.48/0.70          | ~ (r1_xboole_0 @ X7 @ X10))),
% 0.48/0.70      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.48/0.70  thf('24', plain,
% 0.48/0.70      (![X45 : $i, X46 : $i]:
% 0.48/0.70         ((k1_setfam_1 @ (k2_tarski @ X45 @ X46)) = (k3_xboole_0 @ X45 @ X46))),
% 0.48/0.70      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.48/0.70  thf('25', plain,
% 0.48/0.70      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.48/0.70         (~ (r2_hidden @ X9 @ (k1_setfam_1 @ (k2_tarski @ X7 @ X10)))
% 0.48/0.70          | ~ (r1_xboole_0 @ X7 @ X10))),
% 0.48/0.70      inference('demod', [status(thm)], ['23', '24'])).
% 0.48/0.70  thf('26', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]:
% 0.48/0.70         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['22', '25'])).
% 0.48/0.70  thf('27', plain,
% 0.48/0.70      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['19', '26'])).
% 0.48/0.70  thf('28', plain,
% 0.48/0.70      (![X0 : $i]: (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['18', '27'])).
% 0.48/0.70  thf(l13_xboole_0, axiom,
% 0.48/0.70    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.48/0.70  thf('29', plain,
% 0.48/0.70      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.48/0.70      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.48/0.70  thf('30', plain,
% 0.48/0.70      (![X0 : $i]: ((k2_zfmisc_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['28', '29'])).
% 0.48/0.70  thf(t2_boole, axiom,
% 0.48/0.70    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.48/0.70  thf('31', plain,
% 0.48/0.70      (![X11 : $i]: ((k3_xboole_0 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.48/0.70      inference('cnf', [status(esa)], [t2_boole])).
% 0.48/0.70  thf('32', plain,
% 0.48/0.70      (![X45 : $i, X46 : $i]:
% 0.48/0.70         ((k1_setfam_1 @ (k2_tarski @ X45 @ X46)) = (k3_xboole_0 @ X45 @ X46))),
% 0.48/0.70      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.48/0.70  thf('33', plain,
% 0.48/0.70      (![X11 : $i]:
% 0.48/0.70         ((k1_setfam_1 @ (k2_tarski @ X11 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.48/0.70      inference('demod', [status(thm)], ['31', '32'])).
% 0.48/0.70  thf('34', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.48/0.70          | ~ (v1_relat_1 @ X0)
% 0.48/0.70          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.48/0.70      inference('demod', [status(thm)], ['15', '30', '33'])).
% 0.48/0.70  thf('35', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (v1_relat_1 @ k1_xboole_0)
% 0.48/0.70          | ~ (v1_relat_1 @ X0)
% 0.48/0.70          | ~ (v1_relat_1 @ X0)
% 0.48/0.70          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.48/0.70      inference('sup-', [status(thm)], ['1', '34'])).
% 0.48/0.70  thf('36', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.48/0.70          | ~ (v1_relat_1 @ X0)
% 0.48/0.70          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.48/0.70      inference('simplify', [status(thm)], ['35'])).
% 0.48/0.70  thf('37', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.48/0.70          | ~ (v1_relat_1 @ X0)
% 0.48/0.70          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.48/0.70      inference('sup-', [status(thm)], ['0', '36'])).
% 0.48/0.70  thf('38', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.48/0.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.48/0.70  thf('39', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (v1_relat_1 @ X0)
% 0.48/0.70          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.48/0.70      inference('demod', [status(thm)], ['37', '38'])).
% 0.48/0.70  thf('40', plain,
% 0.48/0.70      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.48/0.70      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.48/0.70  thf('41', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.48/0.70      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.48/0.70  thf('42', plain,
% 0.48/0.70      (![X0 : $i]: (((k1_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.48/0.70      inference('sup+', [status(thm)], ['40', '41'])).
% 0.48/0.70  thf('43', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.48/0.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.48/0.70  thf('44', plain,
% 0.48/0.70      (![X0 : $i]: ((v1_xboole_0 @ (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.48/0.70      inference('sup+', [status(thm)], ['42', '43'])).
% 0.48/0.70  thf('45', plain,
% 0.48/0.70      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.48/0.70      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.48/0.70  thf('46', plain, (![X13 : $i]: (r1_xboole_0 @ X13 @ k1_xboole_0)),
% 0.48/0.70      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.48/0.70  thf('47', plain,
% 0.48/0.70      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.48/0.70         ((r1_xboole_0 @ (k2_zfmisc_1 @ X41 @ X42) @ (k2_zfmisc_1 @ X43 @ X44))
% 0.48/0.70          | ~ (r1_xboole_0 @ X41 @ X43))),
% 0.48/0.70      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.48/0.70  thf('48', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.70         (r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X2) @ 
% 0.48/0.70          (k2_zfmisc_1 @ k1_xboole_0 @ X1))),
% 0.48/0.70      inference('sup-', [status(thm)], ['46', '47'])).
% 0.48/0.70  thf('49', plain,
% 0.48/0.70      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['19', '26'])).
% 0.48/0.70  thf('50', plain,
% 0.48/0.70      (![X0 : $i]: (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['48', '49'])).
% 0.48/0.70  thf('51', plain,
% 0.48/0.70      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.48/0.70      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.48/0.70  thf('52', plain,
% 0.48/0.70      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['50', '51'])).
% 0.48/0.70  thf('53', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]:
% 0.48/0.70         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.48/0.70      inference('sup+', [status(thm)], ['45', '52'])).
% 0.48/0.70  thf('54', plain,
% 0.48/0.70      (![X50 : $i]:
% 0.48/0.70         (((k1_setfam_1 @ 
% 0.48/0.70            (k2_tarski @ X50 @ 
% 0.48/0.70             (k2_zfmisc_1 @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X50))))
% 0.48/0.70            = (X50))
% 0.48/0.70          | ~ (v1_relat_1 @ X50))),
% 0.48/0.70      inference('demod', [status(thm)], ['12', '13'])).
% 0.48/0.70  thf('55', plain,
% 0.48/0.70      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.48/0.70      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.48/0.70  thf('56', plain,
% 0.48/0.70      (![X11 : $i]:
% 0.48/0.70         ((k1_setfam_1 @ (k2_tarski @ X11 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.48/0.70      inference('demod', [status(thm)], ['31', '32'])).
% 0.48/0.70  thf('57', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]:
% 0.48/0.70         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k1_xboole_0))
% 0.48/0.70          | ~ (v1_xboole_0 @ X0))),
% 0.48/0.70      inference('sup+', [status(thm)], ['55', '56'])).
% 0.48/0.70  thf(t62_relat_1, conjecture,
% 0.48/0.70    (![A:$i]:
% 0.48/0.70     ( ( v1_relat_1 @ A ) =>
% 0.48/0.70       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.48/0.70         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.48/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.70    (~( ![A:$i]:
% 0.48/0.70        ( ( v1_relat_1 @ A ) =>
% 0.48/0.70          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.48/0.70            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.48/0.70    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.48/0.70  thf('58', plain,
% 0.48/0.70      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.48/0.70        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('59', plain,
% 0.48/0.70      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.48/0.70         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.48/0.70      inference('split', [status(esa)], ['58'])).
% 0.48/0.70  thf('60', plain,
% 0.48/0.70      ((![X0 : $i, X1 : $i]:
% 0.48/0.70          (((k5_relat_1 @ sk_A @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 0.48/0.70             != (k1_xboole_0))
% 0.48/0.70           | ~ (v1_xboole_0 @ X0)))
% 0.48/0.70         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.48/0.70      inference('sup-', [status(thm)], ['57', '59'])).
% 0.48/0.70  thf('61', plain,
% 0.48/0.70      ((![X0 : $i]:
% 0.48/0.70          (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0))
% 0.48/0.70           | ~ (v1_relat_1 @ X0)
% 0.48/0.70           | ~ (v1_xboole_0 @ 
% 0.48/0.70                (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))
% 0.48/0.70         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.48/0.70      inference('sup-', [status(thm)], ['54', '60'])).
% 0.48/0.70  thf('62', plain,
% 0.48/0.70      ((![X0 : $i]:
% 0.48/0.70          (~ (v1_xboole_0 @ k1_xboole_0)
% 0.48/0.70           | ~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.48/0.70           | ~ (v1_relat_1 @ X0)
% 0.48/0.70           | ((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0))))
% 0.48/0.70         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.48/0.70      inference('sup-', [status(thm)], ['53', '61'])).
% 0.48/0.70  thf('63', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.48/0.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.48/0.70  thf('64', plain,
% 0.48/0.70      ((![X0 : $i]:
% 0.48/0.70          (~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.48/0.70           | ~ (v1_relat_1 @ X0)
% 0.48/0.70           | ((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0))))
% 0.48/0.70         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.48/0.70      inference('demod', [status(thm)], ['62', '63'])).
% 0.48/0.70  thf('65', plain,
% 0.48/0.70      ((![X0 : $i]:
% 0.48/0.70          (~ (v1_xboole_0 @ X0)
% 0.48/0.70           | ((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0))
% 0.48/0.70           | ~ (v1_relat_1 @ X0)))
% 0.48/0.70         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.48/0.70      inference('sup-', [status(thm)], ['44', '64'])).
% 0.48/0.70  thf('66', plain, (![X47 : $i]: ((v1_relat_1 @ X47) | ~ (v1_xboole_0 @ X47))),
% 0.48/0.70      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.48/0.70  thf('67', plain,
% 0.48/0.70      (![X48 : $i, X49 : $i]:
% 0.48/0.70         (~ (v1_relat_1 @ X48)
% 0.48/0.70          | ~ (v1_relat_1 @ X49)
% 0.48/0.70          | (v1_relat_1 @ (k5_relat_1 @ X48 @ X49)))),
% 0.48/0.70      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.48/0.70  thf('68', plain, (![X47 : $i]: ((v1_relat_1 @ X47) | ~ (v1_xboole_0 @ X47))),
% 0.48/0.70      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.48/0.70  thf('69', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.48/0.70      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.48/0.70  thf(t46_relat_1, axiom,
% 0.48/0.70    (![A:$i]:
% 0.48/0.70     ( ( v1_relat_1 @ A ) =>
% 0.48/0.70       ( ![B:$i]:
% 0.48/0.70         ( ( v1_relat_1 @ B ) =>
% 0.48/0.70           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.48/0.70             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.48/0.70  thf('70', plain,
% 0.48/0.70      (![X51 : $i, X52 : $i]:
% 0.48/0.70         (~ (v1_relat_1 @ X51)
% 0.48/0.70          | ((k1_relat_1 @ (k5_relat_1 @ X52 @ X51)) = (k1_relat_1 @ X52))
% 0.48/0.70          | ~ (r1_tarski @ (k2_relat_1 @ X52) @ (k1_relat_1 @ X51))
% 0.48/0.70          | ~ (v1_relat_1 @ X52))),
% 0.48/0.70      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.48/0.70  thf('71', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.48/0.70          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.48/0.70          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.48/0.70              = (k1_relat_1 @ k1_xboole_0))
% 0.48/0.70          | ~ (v1_relat_1 @ X0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['69', '70'])).
% 0.48/0.70  thf('72', plain, (![X12 : $i]: (r1_tarski @ k1_xboole_0 @ X12)),
% 0.48/0.70      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.48/0.70  thf('73', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.48/0.70      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.48/0.70  thf('74', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (v1_relat_1 @ k1_xboole_0)
% 0.48/0.70          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.48/0.70          | ~ (v1_relat_1 @ X0))),
% 0.48/0.70      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.48/0.70  thf('75', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.48/0.70          | ~ (v1_relat_1 @ X0)
% 0.48/0.70          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.48/0.70      inference('sup-', [status(thm)], ['68', '74'])).
% 0.48/0.70  thf('76', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.48/0.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.48/0.70  thf('77', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (v1_relat_1 @ X0)
% 0.48/0.70          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.48/0.70      inference('demod', [status(thm)], ['75', '76'])).
% 0.48/0.70  thf('78', plain,
% 0.48/0.70      (![X50 : $i]:
% 0.48/0.70         (((k1_setfam_1 @ 
% 0.48/0.70            (k2_tarski @ X50 @ 
% 0.48/0.70             (k2_zfmisc_1 @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X50))))
% 0.48/0.70            = (X50))
% 0.48/0.70          | ~ (v1_relat_1 @ X50))),
% 0.48/0.70      inference('demod', [status(thm)], ['12', '13'])).
% 0.48/0.70  thf('79', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (((k1_setfam_1 @ 
% 0.48/0.70            (k2_tarski @ (k5_relat_1 @ k1_xboole_0 @ X0) @ 
% 0.48/0.70             (k2_zfmisc_1 @ k1_xboole_0 @ 
% 0.48/0.70              (k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))))
% 0.48/0.70            = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.48/0.70          | ~ (v1_relat_1 @ X0)
% 0.48/0.70          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.48/0.70      inference('sup+', [status(thm)], ['77', '78'])).
% 0.48/0.70  thf('80', plain,
% 0.48/0.70      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['50', '51'])).
% 0.48/0.70  thf('81', plain,
% 0.48/0.70      (![X11 : $i]:
% 0.48/0.70         ((k1_setfam_1 @ (k2_tarski @ X11 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.48/0.70      inference('demod', [status(thm)], ['31', '32'])).
% 0.48/0.70  thf('82', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.48/0.70          | ~ (v1_relat_1 @ X0)
% 0.48/0.70          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.48/0.70      inference('demod', [status(thm)], ['79', '80', '81'])).
% 0.48/0.70  thf('83', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (v1_relat_1 @ X0)
% 0.48/0.70          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.48/0.70          | ~ (v1_relat_1 @ X0)
% 0.48/0.70          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.48/0.70      inference('sup-', [status(thm)], ['67', '82'])).
% 0.48/0.70  thf('84', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.48/0.70          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.48/0.70          | ~ (v1_relat_1 @ X0))),
% 0.48/0.70      inference('simplify', [status(thm)], ['83'])).
% 0.48/0.70  thf('85', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.48/0.70          | ~ (v1_relat_1 @ X0)
% 0.48/0.70          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.48/0.70      inference('sup-', [status(thm)], ['66', '84'])).
% 0.48/0.70  thf('86', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.48/0.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.48/0.70  thf('87', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (v1_relat_1 @ X0)
% 0.48/0.70          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.48/0.70      inference('demod', [status(thm)], ['85', '86'])).
% 0.48/0.70  thf('88', plain,
% 0.48/0.70      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.48/0.70      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.48/0.70  thf('89', plain,
% 0.48/0.70      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.48/0.70         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.48/0.70      inference('split', [status(esa)], ['58'])).
% 0.48/0.70  thf('90', plain,
% 0.48/0.70      ((![X0 : $i]:
% 0.48/0.70          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.48/0.70         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.48/0.70      inference('sup-', [status(thm)], ['88', '89'])).
% 0.48/0.70  thf('91', plain,
% 0.48/0.70      (((((k1_xboole_0) != (k1_xboole_0))
% 0.48/0.70         | ~ (v1_relat_1 @ sk_A)
% 0.48/0.70         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.48/0.70         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.48/0.70      inference('sup-', [status(thm)], ['87', '90'])).
% 0.48/0.70  thf('92', plain, ((v1_relat_1 @ sk_A)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('93', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.48/0.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.48/0.70  thf('94', plain,
% 0.48/0.70      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.48/0.70         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.48/0.70      inference('demod', [status(thm)], ['91', '92', '93'])).
% 0.48/0.70  thf('95', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.48/0.70      inference('simplify', [status(thm)], ['94'])).
% 0.48/0.70  thf('96', plain,
% 0.48/0.70      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.48/0.70       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.48/0.70      inference('split', [status(esa)], ['58'])).
% 0.48/0.70  thf('97', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.48/0.70      inference('sat_resolution*', [status(thm)], ['95', '96'])).
% 0.48/0.70  thf('98', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (~ (v1_xboole_0 @ X0)
% 0.48/0.70          | ((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0))
% 0.48/0.70          | ~ (v1_relat_1 @ X0))),
% 0.48/0.70      inference('simpl_trail', [status(thm)], ['65', '97'])).
% 0.48/0.70  thf('99', plain, (![X47 : $i]: ((v1_relat_1 @ X47) | ~ (v1_xboole_0 @ X47))),
% 0.48/0.70      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.48/0.70  thf('100', plain,
% 0.48/0.70      (![X0 : $i]:
% 0.48/0.70         (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.48/0.70      inference('clc', [status(thm)], ['98', '99'])).
% 0.48/0.70  thf('101', plain,
% 0.48/0.70      ((((k1_xboole_0) != (k1_xboole_0))
% 0.48/0.70        | ~ (v1_relat_1 @ sk_A)
% 0.48/0.70        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.48/0.70      inference('sup-', [status(thm)], ['39', '100'])).
% 0.48/0.70  thf('102', plain, ((v1_relat_1 @ sk_A)),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf('103', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.48/0.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.48/0.70  thf('104', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.48/0.70      inference('demod', [status(thm)], ['101', '102', '103'])).
% 0.48/0.70  thf('105', plain, ($false), inference('simplify', [status(thm)], ['104'])).
% 0.48/0.70  
% 0.48/0.70  % SZS output end Refutation
% 0.48/0.70  
% 0.48/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
