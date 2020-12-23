%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JXwgfMkrJi

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:02 EST 2020

% Result     : Theorem 19.25s
% Output     : Refutation 19.25s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 201 expanded)
%              Number of leaves         :   23 (  73 expanded)
%              Depth                    :   15
%              Number of atoms          :  585 (1547 expanded)
%              Number of equality atoms :   21 (  94 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('2',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_tarski @ X13 @ X15 )
      | ( r1_tarski @ X13 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_tarski @ X13 @ X15 )
      | ( r1_tarski @ X13 @ ( k1_setfam_1 @ ( k2_tarski @ X14 @ X15 ) ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) ) @ X0 )
      | ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('10',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('11',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X11 @ X12 ) ) @ X11 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['9','12'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('14',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('15',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('16',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ ( k1_setfam_1 @ ( k2_tarski @ X16 @ X17 ) ) )
      = X16 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf(t31_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) )).

thf('18',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X20 ) ) @ ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t31_xboole_1])).

thf('19',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('20',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('21',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X18 @ X19 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X18 @ X20 ) ) ) @ ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['17','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t31_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf('25',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v1_relat_1 @ X42 )
      | ( r1_tarski @ ( k3_relat_1 @ X43 ) @ ( k3_relat_1 @ X42 ) )
      | ~ ( r1_tarski @ X43 @ X42 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t31_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('28',plain,(
    ! [X34: $i,X36: $i] :
      ( ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( r1_tarski @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('30',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) )
      | ( v1_relat_1 @ X40 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['26','31'])).

thf('33',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X11 @ X12 ) ) @ X11 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('34',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v1_relat_1 @ X42 )
      | ( r1_tarski @ ( k3_relat_1 @ X43 ) @ ( k3_relat_1 @ X42 ) )
      | ~ ( r1_tarski @ X43 @ X42 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t31_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      | ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('36',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k1_enumset1 @ X22 @ X22 @ X23 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('37',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k1_enumset1 @ X22 @ X22 @ X23 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('38',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X11 @ X12 ) ) @ X11 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) @ X1 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X34: $i,X36: $i] :
      ( ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( r1_tarski @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k1_enumset1 @ X0 @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) )
      | ( v1_relat_1 @ X40 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k1_setfam_1 @ ( k1_enumset1 @ X0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['35','44'])).

thf('46',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_tarski @ X13 @ X15 )
      | ( r1_tarski @ X13 @ ( k1_setfam_1 @ ( k2_tarski @ X14 @ X15 ) ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k3_relat_1 @ X0 ) @ X2 ) ) )
      | ~ ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k3_relat_1 @ X1 ) @ ( k3_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','47'])).

thf(t34_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_relat_1])).

thf('49',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('51',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('52',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['48','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['53','54','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JXwgfMkrJi
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:57:39 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 19.25/19.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 19.25/19.47  % Solved by: fo/fo7.sh
% 19.25/19.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 19.25/19.47  % done 22184 iterations in 19.011s
% 19.25/19.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 19.25/19.47  % SZS output start Refutation
% 19.25/19.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 19.25/19.47  thf(sk_B_type, type, sk_B: $i).
% 19.25/19.47  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 19.25/19.47  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 19.25/19.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 19.25/19.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 19.25/19.47  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 19.25/19.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 19.25/19.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 19.25/19.47  thf(sk_A_type, type, sk_A: $i).
% 19.25/19.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 19.25/19.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 19.25/19.47  thf(d10_xboole_0, axiom,
% 19.25/19.47    (![A:$i,B:$i]:
% 19.25/19.47     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 19.25/19.47  thf('0', plain,
% 19.25/19.47      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 19.25/19.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 19.25/19.47  thf('1', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 19.25/19.47      inference('simplify', [status(thm)], ['0'])).
% 19.25/19.47  thf('2', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 19.25/19.47      inference('simplify', [status(thm)], ['0'])).
% 19.25/19.47  thf(t19_xboole_1, axiom,
% 19.25/19.47    (![A:$i,B:$i,C:$i]:
% 19.25/19.47     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 19.25/19.47       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 19.25/19.47  thf('3', plain,
% 19.25/19.47      (![X13 : $i, X14 : $i, X15 : $i]:
% 19.25/19.47         (~ (r1_tarski @ X13 @ X14)
% 19.25/19.47          | ~ (r1_tarski @ X13 @ X15)
% 19.25/19.47          | (r1_tarski @ X13 @ (k3_xboole_0 @ X14 @ X15)))),
% 19.25/19.47      inference('cnf', [status(esa)], [t19_xboole_1])).
% 19.25/19.47  thf(t12_setfam_1, axiom,
% 19.25/19.47    (![A:$i,B:$i]:
% 19.25/19.47     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 19.25/19.47  thf('4', plain,
% 19.25/19.47      (![X32 : $i, X33 : $i]:
% 19.25/19.47         ((k1_setfam_1 @ (k2_tarski @ X32 @ X33)) = (k3_xboole_0 @ X32 @ X33))),
% 19.25/19.47      inference('cnf', [status(esa)], [t12_setfam_1])).
% 19.25/19.47  thf('5', plain,
% 19.25/19.47      (![X13 : $i, X14 : $i, X15 : $i]:
% 19.25/19.47         (~ (r1_tarski @ X13 @ X14)
% 19.25/19.47          | ~ (r1_tarski @ X13 @ X15)
% 19.25/19.47          | (r1_tarski @ X13 @ (k1_setfam_1 @ (k2_tarski @ X14 @ X15))))),
% 19.25/19.47      inference('demod', [status(thm)], ['3', '4'])).
% 19.25/19.47  thf('6', plain,
% 19.25/19.47      (![X0 : $i, X1 : $i]:
% 19.25/19.47         ((r1_tarski @ X0 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 19.25/19.47          | ~ (r1_tarski @ X0 @ X1))),
% 19.25/19.47      inference('sup-', [status(thm)], ['2', '5'])).
% 19.25/19.47  thf('7', plain,
% 19.25/19.47      (![X0 : $i]: (r1_tarski @ X0 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X0)))),
% 19.25/19.47      inference('sup-', [status(thm)], ['1', '6'])).
% 19.25/19.47  thf('8', plain,
% 19.25/19.47      (![X8 : $i, X10 : $i]:
% 19.25/19.47         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 19.25/19.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 19.25/19.47  thf('9', plain,
% 19.25/19.47      (![X0 : $i]:
% 19.25/19.47         (~ (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X0)) @ X0)
% 19.25/19.47          | ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0)))),
% 19.25/19.47      inference('sup-', [status(thm)], ['7', '8'])).
% 19.25/19.47  thf(t17_xboole_1, axiom,
% 19.25/19.47    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 19.25/19.47  thf('10', plain,
% 19.25/19.47      (![X11 : $i, X12 : $i]: (r1_tarski @ (k3_xboole_0 @ X11 @ X12) @ X11)),
% 19.25/19.47      inference('cnf', [status(esa)], [t17_xboole_1])).
% 19.25/19.47  thf('11', plain,
% 19.25/19.47      (![X32 : $i, X33 : $i]:
% 19.25/19.47         ((k1_setfam_1 @ (k2_tarski @ X32 @ X33)) = (k3_xboole_0 @ X32 @ X33))),
% 19.25/19.47      inference('cnf', [status(esa)], [t12_setfam_1])).
% 19.25/19.47  thf('12', plain,
% 19.25/19.47      (![X11 : $i, X12 : $i]:
% 19.25/19.47         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X11 @ X12)) @ X11)),
% 19.25/19.47      inference('demod', [status(thm)], ['10', '11'])).
% 19.25/19.47  thf('13', plain,
% 19.25/19.47      (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 19.25/19.47      inference('demod', [status(thm)], ['9', '12'])).
% 19.25/19.47  thf(t22_xboole_1, axiom,
% 19.25/19.47    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 19.25/19.47  thf('14', plain,
% 19.25/19.47      (![X16 : $i, X17 : $i]:
% 19.25/19.47         ((k2_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)) = (X16))),
% 19.25/19.47      inference('cnf', [status(esa)], [t22_xboole_1])).
% 19.25/19.47  thf('15', plain,
% 19.25/19.47      (![X32 : $i, X33 : $i]:
% 19.25/19.47         ((k1_setfam_1 @ (k2_tarski @ X32 @ X33)) = (k3_xboole_0 @ X32 @ X33))),
% 19.25/19.47      inference('cnf', [status(esa)], [t12_setfam_1])).
% 19.25/19.47  thf('16', plain,
% 19.25/19.47      (![X16 : $i, X17 : $i]:
% 19.25/19.47         ((k2_xboole_0 @ X16 @ (k1_setfam_1 @ (k2_tarski @ X16 @ X17))) = (X16))),
% 19.25/19.47      inference('demod', [status(thm)], ['14', '15'])).
% 19.25/19.47  thf('17', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 19.25/19.47      inference('sup+', [status(thm)], ['13', '16'])).
% 19.25/19.47  thf(t31_xboole_1, axiom,
% 19.25/19.47    (![A:$i,B:$i,C:$i]:
% 19.25/19.47     ( r1_tarski @
% 19.25/19.47       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 19.25/19.47       ( k2_xboole_0 @ B @ C ) ))).
% 19.25/19.47  thf('18', plain,
% 19.25/19.47      (![X18 : $i, X19 : $i, X20 : $i]:
% 19.25/19.47         (r1_tarski @ 
% 19.25/19.47          (k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ (k3_xboole_0 @ X18 @ X20)) @ 
% 19.25/19.47          (k2_xboole_0 @ X19 @ X20))),
% 19.25/19.47      inference('cnf', [status(esa)], [t31_xboole_1])).
% 19.25/19.47  thf('19', plain,
% 19.25/19.47      (![X32 : $i, X33 : $i]:
% 19.25/19.47         ((k1_setfam_1 @ (k2_tarski @ X32 @ X33)) = (k3_xboole_0 @ X32 @ X33))),
% 19.25/19.47      inference('cnf', [status(esa)], [t12_setfam_1])).
% 19.25/19.47  thf('20', plain,
% 19.25/19.47      (![X32 : $i, X33 : $i]:
% 19.25/19.47         ((k1_setfam_1 @ (k2_tarski @ X32 @ X33)) = (k3_xboole_0 @ X32 @ X33))),
% 19.25/19.47      inference('cnf', [status(esa)], [t12_setfam_1])).
% 19.25/19.47  thf('21', plain,
% 19.25/19.47      (![X18 : $i, X19 : $i, X20 : $i]:
% 19.25/19.47         (r1_tarski @ 
% 19.25/19.47          (k2_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X18 @ X19)) @ 
% 19.25/19.47           (k1_setfam_1 @ (k2_tarski @ X18 @ X20))) @ 
% 19.25/19.47          (k2_xboole_0 @ X19 @ X20))),
% 19.25/19.47      inference('demod', [status(thm)], ['18', '19', '20'])).
% 19.25/19.47  thf('22', plain,
% 19.25/19.47      (![X0 : $i, X1 : $i]:
% 19.25/19.47         (r1_tarski @ 
% 19.25/19.47          (k2_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 19.25/19.47           (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 19.25/19.47          X0)),
% 19.25/19.47      inference('sup+', [status(thm)], ['17', '21'])).
% 19.25/19.47  thf('23', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 19.25/19.47      inference('sup+', [status(thm)], ['13', '16'])).
% 19.25/19.47  thf('24', plain,
% 19.25/19.47      (![X0 : $i, X1 : $i]:
% 19.25/19.47         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 19.25/19.47      inference('demod', [status(thm)], ['22', '23'])).
% 19.25/19.47  thf(t31_relat_1, axiom,
% 19.25/19.47    (![A:$i]:
% 19.25/19.47     ( ( v1_relat_1 @ A ) =>
% 19.25/19.47       ( ![B:$i]:
% 19.25/19.47         ( ( v1_relat_1 @ B ) =>
% 19.25/19.47           ( ( r1_tarski @ A @ B ) =>
% 19.25/19.47             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 19.25/19.47  thf('25', plain,
% 19.25/19.47      (![X42 : $i, X43 : $i]:
% 19.25/19.47         (~ (v1_relat_1 @ X42)
% 19.25/19.47          | (r1_tarski @ (k3_relat_1 @ X43) @ (k3_relat_1 @ X42))
% 19.25/19.47          | ~ (r1_tarski @ X43 @ X42)
% 19.25/19.47          | ~ (v1_relat_1 @ X43))),
% 19.25/19.47      inference('cnf', [status(esa)], [t31_relat_1])).
% 19.25/19.47  thf('26', plain,
% 19.25/19.47      (![X0 : $i, X1 : $i]:
% 19.25/19.47         (~ (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 19.25/19.47          | (r1_tarski @ 
% 19.25/19.47             (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 19.25/19.47             (k3_relat_1 @ X0))
% 19.25/19.47          | ~ (v1_relat_1 @ X0))),
% 19.25/19.47      inference('sup-', [status(thm)], ['24', '25'])).
% 19.25/19.47  thf('27', plain,
% 19.25/19.47      (![X0 : $i, X1 : $i]:
% 19.25/19.47         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 19.25/19.47      inference('demod', [status(thm)], ['22', '23'])).
% 19.25/19.47  thf(t3_subset, axiom,
% 19.25/19.47    (![A:$i,B:$i]:
% 19.25/19.47     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 19.25/19.47  thf('28', plain,
% 19.25/19.47      (![X34 : $i, X36 : $i]:
% 19.25/19.47         ((m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X36)) | ~ (r1_tarski @ X34 @ X36))),
% 19.25/19.47      inference('cnf', [status(esa)], [t3_subset])).
% 19.25/19.47  thf('29', plain,
% 19.25/19.47      (![X0 : $i, X1 : $i]:
% 19.25/19.47         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 19.25/19.47          (k1_zfmisc_1 @ X0))),
% 19.25/19.47      inference('sup-', [status(thm)], ['27', '28'])).
% 19.25/19.47  thf(cc2_relat_1, axiom,
% 19.25/19.47    (![A:$i]:
% 19.25/19.47     ( ( v1_relat_1 @ A ) =>
% 19.25/19.47       ( ![B:$i]:
% 19.25/19.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 19.25/19.47  thf('30', plain,
% 19.25/19.47      (![X40 : $i, X41 : $i]:
% 19.25/19.47         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 19.25/19.47          | (v1_relat_1 @ X40)
% 19.25/19.47          | ~ (v1_relat_1 @ X41))),
% 19.25/19.47      inference('cnf', [status(esa)], [cc2_relat_1])).
% 19.25/19.47  thf('31', plain,
% 19.25/19.47      (![X0 : $i, X1 : $i]:
% 19.25/19.47         (~ (v1_relat_1 @ X0)
% 19.25/19.47          | (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 19.25/19.47      inference('sup-', [status(thm)], ['29', '30'])).
% 19.25/19.47  thf('32', plain,
% 19.25/19.47      (![X0 : $i, X1 : $i]:
% 19.25/19.47         (~ (v1_relat_1 @ X0)
% 19.25/19.47          | (r1_tarski @ 
% 19.25/19.47             (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 19.25/19.47             (k3_relat_1 @ X0)))),
% 19.25/19.47      inference('clc', [status(thm)], ['26', '31'])).
% 19.25/19.47  thf('33', plain,
% 19.25/19.47      (![X11 : $i, X12 : $i]:
% 19.25/19.47         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X11 @ X12)) @ X11)),
% 19.25/19.47      inference('demod', [status(thm)], ['10', '11'])).
% 19.25/19.47  thf('34', plain,
% 19.25/19.47      (![X42 : $i, X43 : $i]:
% 19.25/19.47         (~ (v1_relat_1 @ X42)
% 19.25/19.47          | (r1_tarski @ (k3_relat_1 @ X43) @ (k3_relat_1 @ X42))
% 19.25/19.47          | ~ (r1_tarski @ X43 @ X42)
% 19.25/19.47          | ~ (v1_relat_1 @ X43))),
% 19.25/19.47      inference('cnf', [status(esa)], [t31_relat_1])).
% 19.25/19.47  thf('35', plain,
% 19.25/19.47      (![X0 : $i, X1 : $i]:
% 19.25/19.47         (~ (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 19.25/19.47          | (r1_tarski @ 
% 19.25/19.47             (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 19.25/19.47             (k3_relat_1 @ X0))
% 19.25/19.47          | ~ (v1_relat_1 @ X0))),
% 19.25/19.47      inference('sup-', [status(thm)], ['33', '34'])).
% 19.25/19.47  thf(t70_enumset1, axiom,
% 19.25/19.47    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 19.25/19.47  thf('36', plain,
% 19.25/19.47      (![X22 : $i, X23 : $i]:
% 19.25/19.47         ((k1_enumset1 @ X22 @ X22 @ X23) = (k2_tarski @ X22 @ X23))),
% 19.25/19.47      inference('cnf', [status(esa)], [t70_enumset1])).
% 19.25/19.47  thf('37', plain,
% 19.25/19.47      (![X22 : $i, X23 : $i]:
% 19.25/19.47         ((k1_enumset1 @ X22 @ X22 @ X23) = (k2_tarski @ X22 @ X23))),
% 19.25/19.47      inference('cnf', [status(esa)], [t70_enumset1])).
% 19.25/19.47  thf('38', plain,
% 19.25/19.47      (![X11 : $i, X12 : $i]:
% 19.25/19.47         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X11 @ X12)) @ X11)),
% 19.25/19.47      inference('demod', [status(thm)], ['10', '11'])).
% 19.25/19.47  thf('39', plain,
% 19.25/19.47      (![X0 : $i, X1 : $i]:
% 19.25/19.47         (r1_tarski @ (k1_setfam_1 @ (k1_enumset1 @ X1 @ X1 @ X0)) @ X1)),
% 19.25/19.47      inference('sup+', [status(thm)], ['37', '38'])).
% 19.25/19.47  thf('40', plain,
% 19.25/19.47      (![X34 : $i, X36 : $i]:
% 19.25/19.47         ((m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X36)) | ~ (r1_tarski @ X34 @ X36))),
% 19.25/19.47      inference('cnf', [status(esa)], [t3_subset])).
% 19.25/19.47  thf('41', plain,
% 19.25/19.47      (![X0 : $i, X1 : $i]:
% 19.25/19.47         (m1_subset_1 @ (k1_setfam_1 @ (k1_enumset1 @ X0 @ X0 @ X1)) @ 
% 19.25/19.47          (k1_zfmisc_1 @ X0))),
% 19.25/19.47      inference('sup-', [status(thm)], ['39', '40'])).
% 19.25/19.47  thf('42', plain,
% 19.25/19.47      (![X40 : $i, X41 : $i]:
% 19.25/19.47         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 19.25/19.47          | (v1_relat_1 @ X40)
% 19.25/19.47          | ~ (v1_relat_1 @ X41))),
% 19.25/19.47      inference('cnf', [status(esa)], [cc2_relat_1])).
% 19.25/19.47  thf('43', plain,
% 19.25/19.47      (![X0 : $i, X1 : $i]:
% 19.25/19.47         (~ (v1_relat_1 @ X0)
% 19.25/19.47          | (v1_relat_1 @ (k1_setfam_1 @ (k1_enumset1 @ X0 @ X0 @ X1))))),
% 19.25/19.47      inference('sup-', [status(thm)], ['41', '42'])).
% 19.25/19.47  thf('44', plain,
% 19.25/19.47      (![X0 : $i, X1 : $i]:
% 19.25/19.47         ((v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 19.25/19.47          | ~ (v1_relat_1 @ X1))),
% 19.25/19.47      inference('sup+', [status(thm)], ['36', '43'])).
% 19.25/19.47  thf('45', plain,
% 19.25/19.47      (![X0 : $i, X1 : $i]:
% 19.25/19.47         (~ (v1_relat_1 @ X0)
% 19.25/19.47          | (r1_tarski @ 
% 19.25/19.47             (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 19.25/19.47             (k3_relat_1 @ X0)))),
% 19.25/19.47      inference('clc', [status(thm)], ['35', '44'])).
% 19.25/19.47  thf('46', plain,
% 19.25/19.47      (![X13 : $i, X14 : $i, X15 : $i]:
% 19.25/19.47         (~ (r1_tarski @ X13 @ X14)
% 19.25/19.47          | ~ (r1_tarski @ X13 @ X15)
% 19.25/19.47          | (r1_tarski @ X13 @ (k1_setfam_1 @ (k2_tarski @ X14 @ X15))))),
% 19.25/19.47      inference('demod', [status(thm)], ['3', '4'])).
% 19.25/19.47  thf('47', plain,
% 19.25/19.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.25/19.47         (~ (v1_relat_1 @ X0)
% 19.25/19.47          | (r1_tarski @ 
% 19.25/19.47             (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 19.25/19.47             (k1_setfam_1 @ (k2_tarski @ (k3_relat_1 @ X0) @ X2)))
% 19.25/19.47          | ~ (r1_tarski @ 
% 19.25/19.47               (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ X2))),
% 19.25/19.47      inference('sup-', [status(thm)], ['45', '46'])).
% 19.25/19.47  thf('48', plain,
% 19.25/19.47      (![X0 : $i, X1 : $i]:
% 19.25/19.47         (~ (v1_relat_1 @ X0)
% 19.25/19.47          | (r1_tarski @ 
% 19.25/19.47             (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 19.25/19.47             (k1_setfam_1 @ (k2_tarski @ (k3_relat_1 @ X1) @ (k3_relat_1 @ X0))))
% 19.25/19.47          | ~ (v1_relat_1 @ X1))),
% 19.25/19.47      inference('sup-', [status(thm)], ['32', '47'])).
% 19.25/19.47  thf(t34_relat_1, conjecture,
% 19.25/19.47    (![A:$i]:
% 19.25/19.47     ( ( v1_relat_1 @ A ) =>
% 19.25/19.47       ( ![B:$i]:
% 19.25/19.47         ( ( v1_relat_1 @ B ) =>
% 19.25/19.47           ( r1_tarski @
% 19.25/19.47             ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 19.25/19.47             ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 19.25/19.47  thf(zf_stmt_0, negated_conjecture,
% 19.25/19.47    (~( ![A:$i]:
% 19.25/19.47        ( ( v1_relat_1 @ A ) =>
% 19.25/19.47          ( ![B:$i]:
% 19.25/19.47            ( ( v1_relat_1 @ B ) =>
% 19.25/19.47              ( r1_tarski @
% 19.25/19.47                ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 19.25/19.47                ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 19.25/19.47    inference('cnf.neg', [status(esa)], [t34_relat_1])).
% 19.25/19.47  thf('49', plain,
% 19.25/19.47      (~ (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 19.25/19.47          (k3_xboole_0 @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 19.25/19.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.25/19.47  thf('50', plain,
% 19.25/19.47      (![X32 : $i, X33 : $i]:
% 19.25/19.47         ((k1_setfam_1 @ (k2_tarski @ X32 @ X33)) = (k3_xboole_0 @ X32 @ X33))),
% 19.25/19.47      inference('cnf', [status(esa)], [t12_setfam_1])).
% 19.25/19.47  thf('51', plain,
% 19.25/19.47      (![X32 : $i, X33 : $i]:
% 19.25/19.47         ((k1_setfam_1 @ (k2_tarski @ X32 @ X33)) = (k3_xboole_0 @ X32 @ X33))),
% 19.25/19.47      inference('cnf', [status(esa)], [t12_setfam_1])).
% 19.25/19.47  thf('52', plain,
% 19.25/19.47      (~ (r1_tarski @ 
% 19.25/19.47          (k3_relat_1 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))) @ 
% 19.25/19.47          (k1_setfam_1 @ 
% 19.25/19.47           (k2_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))))),
% 19.25/19.47      inference('demod', [status(thm)], ['49', '50', '51'])).
% 19.25/19.47  thf('53', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 19.25/19.47      inference('sup-', [status(thm)], ['48', '52'])).
% 19.25/19.47  thf('54', plain, ((v1_relat_1 @ sk_A)),
% 19.25/19.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.25/19.47  thf('55', plain, ((v1_relat_1 @ sk_B)),
% 19.25/19.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.25/19.47  thf('56', plain, ($false),
% 19.25/19.47      inference('demod', [status(thm)], ['53', '54', '55'])).
% 19.25/19.47  
% 19.25/19.47  % SZS output end Refutation
% 19.25/19.47  
% 19.25/19.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
