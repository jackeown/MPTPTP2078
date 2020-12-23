%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OBLPlF2iqT

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:01 EST 2020

% Result     : Theorem 3.44s
% Output     : Refutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 100 expanded)
%              Number of leaves         :   25 (  39 expanded)
%              Depth                    :   15
%              Number of atoms          :  721 ( 907 expanded)
%              Number of equality atoms :   46 (  64 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X51 @ X52 ) @ X53 )
        = ( k7_relat_1 @ X51 @ ( k3_xboole_0 @ X52 @ X53 ) ) )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X42 @ X43 ) )
      = ( k3_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X51 @ X52 ) @ X53 )
        = ( k7_relat_1 @ X51 @ ( k1_setfam_1 @ ( k2_tarski @ X52 @ X53 ) ) ) )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('4',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('5',plain,(
    ! [X68: $i,X69: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X68 ) @ X69 )
      | ( ( k7_relat_1 @ X68 @ X69 )
        = X68 )
      | ~ ( v1_relat_1 @ X68 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) )
        = ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','6'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( v1_relat_1 @ X46 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X46 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) )
        = ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X51 @ X52 ) @ X53 )
        = ( k7_relat_1 @ X51 @ ( k1_setfam_1 @ ( k2_tarski @ X52 @ X53 ) ) ) )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('11',plain,(
    ! [X64: $i,X65: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X64 @ X65 ) @ X64 )
      | ~ ( v1_relat_1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('13',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X42 @ X43 ) )
      = ( k3_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_setfam_1 @ ( k2_tarski @ ( k7_relat_1 @ X0 @ X1 ) @ X0 ) )
        = ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ ( k7_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k7_relat_1 @ X2 @ X1 ) ) )
        = ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( v1_relat_1 @ X46 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X46 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k1_setfam_1 @ ( k2_tarski @ ( k7_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k7_relat_1 @ X2 @ X1 ) ) )
        = ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','18'])).

thf('20',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('21',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X1 @ X0 )
        = ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('26',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X44 ) @ X45 )
      | ( v4_relat_1 @ X44 @ X45 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(fc23_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v4_relat_1 @ C @ B ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ C @ A ) )
        & ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ A )
        & ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) ) ) )).

thf('28',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( v4_relat_1 @ ( k7_relat_1 @ X48 @ X49 ) @ X49 )
      | ~ ( v4_relat_1 @ X48 @ X50 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[fc23_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( v4_relat_1 @ X44 @ X45 )
      | ( r1_tarski @ ( k1_relat_1 @ X44 ) @ X45 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( v1_relat_1 @ X46 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X46 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf(t103_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k7_relat_1 @ C @ A ) ) ) ) )).

thf('35',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ~ ( r1_tarski @ X54 @ X55 )
      | ~ ( v1_relat_1 @ X56 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X56 @ X55 ) @ X54 )
        = ( k7_relat_1 @ X56 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[t103_relat_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k7_relat_1 @ X2 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X1 @ X0 )
        = ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf(t212_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('39',plain,(
    ! [X62: $i,X63: $i] :
      ( ( ( k1_relat_1 @ ( k6_subset_1 @ X62 @ ( k7_relat_1 @ X62 @ X63 ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ X62 ) @ X63 ) )
      | ~ ( v1_relat_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t212_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('40',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k6_subset_1 @ X40 @ X41 )
      = ( k4_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('41',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k6_subset_1 @ X40 @ X41 )
      = ( k4_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('42',plain,(
    ! [X62: $i,X63: $i] :
      ( ( ( k1_relat_1 @ ( k4_xboole_0 @ X62 @ ( k7_relat_1 @ X62 @ X63 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X62 ) @ X63 ) )
      | ~ ( v1_relat_1 @ X62 ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k4_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k4_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf(t213_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k6_subset_1 @ ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) )
        = ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( k6_subset_1 @ ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) )
          = ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t213_relat_1])).

thf('45',plain,(
    ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
 != ( k1_relat_1 @ ( k6_subset_1 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k6_subset_1 @ X40 @ X41 )
      = ( k4_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('47',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k6_subset_1 @ X40 @ X41 )
      = ( k4_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('48',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
     != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['44','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    $false ),
    inference(simplify,[status(thm)],['51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OBLPlF2iqT
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:18:31 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 3.44/3.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.44/3.64  % Solved by: fo/fo7.sh
% 3.44/3.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.44/3.64  % done 2895 iterations in 3.182s
% 3.44/3.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.44/3.64  % SZS output start Refutation
% 3.44/3.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.44/3.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.44/3.64  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.44/3.64  thf(sk_A_type, type, sk_A: $i).
% 3.44/3.64  thf(sk_B_type, type, sk_B: $i).
% 3.44/3.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.44/3.64  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 3.44/3.64  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 3.44/3.64  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.44/3.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.44/3.64  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.44/3.64  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 3.44/3.64  thf(t100_relat_1, axiom,
% 3.44/3.64    (![A:$i,B:$i,C:$i]:
% 3.44/3.64     ( ( v1_relat_1 @ C ) =>
% 3.44/3.64       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 3.44/3.64         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 3.44/3.64  thf('0', plain,
% 3.44/3.64      (![X51 : $i, X52 : $i, X53 : $i]:
% 3.44/3.64         (((k7_relat_1 @ (k7_relat_1 @ X51 @ X52) @ X53)
% 3.44/3.64            = (k7_relat_1 @ X51 @ (k3_xboole_0 @ X52 @ X53)))
% 3.44/3.64          | ~ (v1_relat_1 @ X51))),
% 3.44/3.64      inference('cnf', [status(esa)], [t100_relat_1])).
% 3.44/3.64  thf(t12_setfam_1, axiom,
% 3.44/3.64    (![A:$i,B:$i]:
% 3.44/3.64     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 3.44/3.64  thf('1', plain,
% 3.44/3.64      (![X42 : $i, X43 : $i]:
% 3.44/3.64         ((k1_setfam_1 @ (k2_tarski @ X42 @ X43)) = (k3_xboole_0 @ X42 @ X43))),
% 3.44/3.64      inference('cnf', [status(esa)], [t12_setfam_1])).
% 3.44/3.64  thf('2', plain,
% 3.44/3.64      (![X51 : $i, X52 : $i, X53 : $i]:
% 3.44/3.64         (((k7_relat_1 @ (k7_relat_1 @ X51 @ X52) @ X53)
% 3.44/3.64            = (k7_relat_1 @ X51 @ (k1_setfam_1 @ (k2_tarski @ X52 @ X53))))
% 3.44/3.64          | ~ (v1_relat_1 @ X51))),
% 3.44/3.64      inference('demod', [status(thm)], ['0', '1'])).
% 3.44/3.64  thf(d10_xboole_0, axiom,
% 3.44/3.64    (![A:$i,B:$i]:
% 3.44/3.64     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.44/3.64  thf('3', plain,
% 3.44/3.64      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 3.44/3.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.44/3.64  thf('4', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 3.44/3.64      inference('simplify', [status(thm)], ['3'])).
% 3.44/3.64  thf(t97_relat_1, axiom,
% 3.44/3.64    (![A:$i,B:$i]:
% 3.44/3.64     ( ( v1_relat_1 @ B ) =>
% 3.44/3.64       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 3.44/3.64         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 3.44/3.64  thf('5', plain,
% 3.44/3.64      (![X68 : $i, X69 : $i]:
% 3.44/3.64         (~ (r1_tarski @ (k1_relat_1 @ X68) @ X69)
% 3.44/3.64          | ((k7_relat_1 @ X68 @ X69) = (X68))
% 3.44/3.64          | ~ (v1_relat_1 @ X68))),
% 3.44/3.64      inference('cnf', [status(esa)], [t97_relat_1])).
% 3.44/3.64  thf('6', plain,
% 3.44/3.64      (![X0 : $i]:
% 3.44/3.64         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 3.44/3.64      inference('sup-', [status(thm)], ['4', '5'])).
% 3.44/3.64  thf('7', plain,
% 3.44/3.64      (![X0 : $i, X1 : $i]:
% 3.44/3.64         (((k7_relat_1 @ X1 @ 
% 3.44/3.64            (k1_setfam_1 @ 
% 3.44/3.64             (k2_tarski @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))))
% 3.44/3.64            = (k7_relat_1 @ X1 @ X0))
% 3.44/3.64          | ~ (v1_relat_1 @ X1)
% 3.44/3.64          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 3.44/3.64      inference('sup+', [status(thm)], ['2', '6'])).
% 3.44/3.64  thf(dt_k7_relat_1, axiom,
% 3.44/3.64    (![A:$i,B:$i]:
% 3.44/3.64     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 3.44/3.64  thf('8', plain,
% 3.44/3.64      (![X46 : $i, X47 : $i]:
% 3.44/3.64         (~ (v1_relat_1 @ X46) | (v1_relat_1 @ (k7_relat_1 @ X46 @ X47)))),
% 3.44/3.64      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 3.44/3.64  thf('9', plain,
% 3.44/3.64      (![X0 : $i, X1 : $i]:
% 3.44/3.64         (~ (v1_relat_1 @ X1)
% 3.44/3.64          | ((k7_relat_1 @ X1 @ 
% 3.44/3.64              (k1_setfam_1 @ 
% 3.44/3.64               (k2_tarski @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))))
% 3.44/3.64              = (k7_relat_1 @ X1 @ X0)))),
% 3.44/3.64      inference('clc', [status(thm)], ['7', '8'])).
% 3.44/3.64  thf('10', plain,
% 3.44/3.64      (![X51 : $i, X52 : $i, X53 : $i]:
% 3.44/3.64         (((k7_relat_1 @ (k7_relat_1 @ X51 @ X52) @ X53)
% 3.44/3.64            = (k7_relat_1 @ X51 @ (k1_setfam_1 @ (k2_tarski @ X52 @ X53))))
% 3.44/3.64          | ~ (v1_relat_1 @ X51))),
% 3.44/3.64      inference('demod', [status(thm)], ['0', '1'])).
% 3.44/3.64  thf(t88_relat_1, axiom,
% 3.44/3.64    (![A:$i,B:$i]:
% 3.44/3.64     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 3.44/3.64  thf('11', plain,
% 3.44/3.64      (![X64 : $i, X65 : $i]:
% 3.44/3.64         ((r1_tarski @ (k7_relat_1 @ X64 @ X65) @ X64) | ~ (v1_relat_1 @ X64))),
% 3.44/3.64      inference('cnf', [status(esa)], [t88_relat_1])).
% 3.44/3.64  thf(t28_xboole_1, axiom,
% 3.44/3.64    (![A:$i,B:$i]:
% 3.44/3.64     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 3.44/3.64  thf('12', plain,
% 3.44/3.64      (![X10 : $i, X11 : $i]:
% 3.44/3.64         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 3.44/3.64      inference('cnf', [status(esa)], [t28_xboole_1])).
% 3.44/3.64  thf('13', plain,
% 3.44/3.64      (![X42 : $i, X43 : $i]:
% 3.44/3.64         ((k1_setfam_1 @ (k2_tarski @ X42 @ X43)) = (k3_xboole_0 @ X42 @ X43))),
% 3.44/3.64      inference('cnf', [status(esa)], [t12_setfam_1])).
% 3.44/3.64  thf('14', plain,
% 3.44/3.64      (![X10 : $i, X11 : $i]:
% 3.44/3.64         (((k1_setfam_1 @ (k2_tarski @ X10 @ X11)) = (X10))
% 3.44/3.64          | ~ (r1_tarski @ X10 @ X11))),
% 3.44/3.64      inference('demod', [status(thm)], ['12', '13'])).
% 3.44/3.64  thf('15', plain,
% 3.44/3.64      (![X0 : $i, X1 : $i]:
% 3.44/3.64         (~ (v1_relat_1 @ X0)
% 3.44/3.64          | ((k1_setfam_1 @ (k2_tarski @ (k7_relat_1 @ X0 @ X1) @ X0))
% 3.44/3.64              = (k7_relat_1 @ X0 @ X1)))),
% 3.44/3.64      inference('sup-', [status(thm)], ['11', '14'])).
% 3.44/3.64  thf('16', plain,
% 3.44/3.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.44/3.64         (((k1_setfam_1 @ 
% 3.44/3.64            (k2_tarski @ 
% 3.44/3.64             (k7_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 3.44/3.64             (k7_relat_1 @ X2 @ X1)))
% 3.44/3.64            = (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 3.44/3.64          | ~ (v1_relat_1 @ X2)
% 3.44/3.64          | ~ (v1_relat_1 @ (k7_relat_1 @ X2 @ X1)))),
% 3.44/3.64      inference('sup+', [status(thm)], ['10', '15'])).
% 3.44/3.64  thf('17', plain,
% 3.44/3.64      (![X46 : $i, X47 : $i]:
% 3.44/3.64         (~ (v1_relat_1 @ X46) | (v1_relat_1 @ (k7_relat_1 @ X46 @ X47)))),
% 3.44/3.64      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 3.44/3.64  thf('18', plain,
% 3.44/3.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.44/3.64         (~ (v1_relat_1 @ X2)
% 3.44/3.64          | ((k1_setfam_1 @ 
% 3.44/3.64              (k2_tarski @ 
% 3.44/3.64               (k7_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 3.44/3.64               (k7_relat_1 @ X2 @ X1)))
% 3.44/3.64              = (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)))),
% 3.44/3.64      inference('clc', [status(thm)], ['16', '17'])).
% 3.44/3.64  thf('19', plain,
% 3.44/3.64      (![X0 : $i, X1 : $i]:
% 3.44/3.64         (((k1_setfam_1 @ 
% 3.44/3.64            (k2_tarski @ (k7_relat_1 @ X1 @ X0) @ (k7_relat_1 @ X1 @ X0)))
% 3.44/3.64            = (k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 3.44/3.64               (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 3.44/3.64          | ~ (v1_relat_1 @ X1)
% 3.44/3.64          | ~ (v1_relat_1 @ X1))),
% 3.44/3.64      inference('sup+', [status(thm)], ['9', '18'])).
% 3.44/3.64  thf('20', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 3.44/3.64      inference('simplify', [status(thm)], ['3'])).
% 3.44/3.64  thf('21', plain,
% 3.44/3.64      (![X10 : $i, X11 : $i]:
% 3.44/3.64         (((k1_setfam_1 @ (k2_tarski @ X10 @ X11)) = (X10))
% 3.44/3.64          | ~ (r1_tarski @ X10 @ X11))),
% 3.44/3.64      inference('demod', [status(thm)], ['12', '13'])).
% 3.44/3.64  thf('22', plain,
% 3.44/3.64      (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 3.44/3.64      inference('sup-', [status(thm)], ['20', '21'])).
% 3.44/3.64  thf('23', plain,
% 3.44/3.64      (![X0 : $i, X1 : $i]:
% 3.44/3.64         (((k7_relat_1 @ X1 @ X0)
% 3.44/3.64            = (k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 3.44/3.64               (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 3.44/3.64          | ~ (v1_relat_1 @ X1)
% 3.44/3.64          | ~ (v1_relat_1 @ X1))),
% 3.44/3.64      inference('demod', [status(thm)], ['19', '22'])).
% 3.44/3.64  thf('24', plain,
% 3.44/3.64      (![X0 : $i, X1 : $i]:
% 3.44/3.64         (~ (v1_relat_1 @ X1)
% 3.44/3.64          | ((k7_relat_1 @ X1 @ X0)
% 3.44/3.64              = (k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 3.44/3.64                 (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))))),
% 3.44/3.64      inference('simplify', [status(thm)], ['23'])).
% 3.44/3.64  thf('25', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 3.44/3.64      inference('simplify', [status(thm)], ['3'])).
% 3.44/3.64  thf(d18_relat_1, axiom,
% 3.44/3.64    (![A:$i,B:$i]:
% 3.44/3.64     ( ( v1_relat_1 @ B ) =>
% 3.44/3.64       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 3.44/3.64  thf('26', plain,
% 3.44/3.64      (![X44 : $i, X45 : $i]:
% 3.44/3.64         (~ (r1_tarski @ (k1_relat_1 @ X44) @ X45)
% 3.44/3.64          | (v4_relat_1 @ X44 @ X45)
% 3.44/3.64          | ~ (v1_relat_1 @ X44))),
% 3.44/3.64      inference('cnf', [status(esa)], [d18_relat_1])).
% 3.44/3.64  thf('27', plain,
% 3.44/3.64      (![X0 : $i]:
% 3.44/3.64         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 3.44/3.64      inference('sup-', [status(thm)], ['25', '26'])).
% 3.44/3.64  thf(fc23_relat_1, axiom,
% 3.44/3.64    (![A:$i,B:$i,C:$i]:
% 3.44/3.64     ( ( ( v1_relat_1 @ C ) & ( v4_relat_1 @ C @ B ) ) =>
% 3.44/3.64       ( ( v1_relat_1 @ ( k7_relat_1 @ C @ A ) ) & 
% 3.44/3.64         ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ A ) & 
% 3.44/3.64         ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) ) ))).
% 3.44/3.64  thf('28', plain,
% 3.44/3.64      (![X48 : $i, X49 : $i, X50 : $i]:
% 3.44/3.64         ((v4_relat_1 @ (k7_relat_1 @ X48 @ X49) @ X49)
% 3.44/3.64          | ~ (v4_relat_1 @ X48 @ X50)
% 3.44/3.64          | ~ (v1_relat_1 @ X48))),
% 3.44/3.64      inference('cnf', [status(esa)], [fc23_relat_1])).
% 3.44/3.64  thf('29', plain,
% 3.44/3.64      (![X0 : $i, X1 : $i]:
% 3.44/3.64         (~ (v1_relat_1 @ X0)
% 3.44/3.64          | ~ (v1_relat_1 @ X0)
% 3.44/3.64          | (v4_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X1))),
% 3.44/3.64      inference('sup-', [status(thm)], ['27', '28'])).
% 3.44/3.64  thf('30', plain,
% 3.44/3.64      (![X0 : $i, X1 : $i]:
% 3.44/3.64         ((v4_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X1) | ~ (v1_relat_1 @ X0))),
% 3.44/3.64      inference('simplify', [status(thm)], ['29'])).
% 3.44/3.64  thf('31', plain,
% 3.44/3.64      (![X44 : $i, X45 : $i]:
% 3.44/3.64         (~ (v4_relat_1 @ X44 @ X45)
% 3.44/3.64          | (r1_tarski @ (k1_relat_1 @ X44) @ X45)
% 3.44/3.64          | ~ (v1_relat_1 @ X44))),
% 3.44/3.64      inference('cnf', [status(esa)], [d18_relat_1])).
% 3.44/3.64  thf('32', plain,
% 3.44/3.64      (![X0 : $i, X1 : $i]:
% 3.44/3.64         (~ (v1_relat_1 @ X1)
% 3.44/3.64          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 3.44/3.64          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0))),
% 3.44/3.64      inference('sup-', [status(thm)], ['30', '31'])).
% 3.44/3.64  thf('33', plain,
% 3.44/3.64      (![X46 : $i, X47 : $i]:
% 3.44/3.64         (~ (v1_relat_1 @ X46) | (v1_relat_1 @ (k7_relat_1 @ X46 @ X47)))),
% 3.44/3.64      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 3.44/3.64  thf('34', plain,
% 3.44/3.64      (![X0 : $i, X1 : $i]:
% 3.44/3.64         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0)
% 3.44/3.64          | ~ (v1_relat_1 @ X1))),
% 3.44/3.64      inference('clc', [status(thm)], ['32', '33'])).
% 3.44/3.64  thf(t103_relat_1, axiom,
% 3.44/3.64    (![A:$i,B:$i,C:$i]:
% 3.44/3.64     ( ( v1_relat_1 @ C ) =>
% 3.44/3.64       ( ( r1_tarski @ A @ B ) =>
% 3.44/3.64         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k7_relat_1 @ C @ A ) ) ) ))).
% 3.44/3.64  thf('35', plain,
% 3.44/3.64      (![X54 : $i, X55 : $i, X56 : $i]:
% 3.44/3.64         (~ (r1_tarski @ X54 @ X55)
% 3.44/3.64          | ~ (v1_relat_1 @ X56)
% 3.44/3.64          | ((k7_relat_1 @ (k7_relat_1 @ X56 @ X55) @ X54)
% 3.44/3.64              = (k7_relat_1 @ X56 @ X54)))),
% 3.44/3.64      inference('cnf', [status(esa)], [t103_relat_1])).
% 3.44/3.64  thf('36', plain,
% 3.44/3.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.44/3.64         (~ (v1_relat_1 @ X1)
% 3.44/3.64          | ((k7_relat_1 @ (k7_relat_1 @ X2 @ X0) @ 
% 3.44/3.64              (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 3.44/3.64              = (k7_relat_1 @ X2 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 3.44/3.64          | ~ (v1_relat_1 @ X2))),
% 3.44/3.64      inference('sup-', [status(thm)], ['34', '35'])).
% 3.44/3.64  thf('37', plain,
% 3.44/3.64      (![X0 : $i, X1 : $i]:
% 3.44/3.64         (((k7_relat_1 @ X1 @ X0)
% 3.44/3.64            = (k7_relat_1 @ X1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 3.44/3.64          | ~ (v1_relat_1 @ X1)
% 3.44/3.64          | ~ (v1_relat_1 @ X1)
% 3.44/3.64          | ~ (v1_relat_1 @ X1))),
% 3.44/3.64      inference('sup+', [status(thm)], ['24', '36'])).
% 3.44/3.64  thf('38', plain,
% 3.44/3.64      (![X0 : $i, X1 : $i]:
% 3.44/3.64         (~ (v1_relat_1 @ X1)
% 3.44/3.64          | ((k7_relat_1 @ X1 @ X0)
% 3.44/3.64              = (k7_relat_1 @ X1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))))),
% 3.44/3.64      inference('simplify', [status(thm)], ['37'])).
% 3.44/3.64  thf(t212_relat_1, axiom,
% 3.44/3.64    (![A:$i,B:$i]:
% 3.44/3.64     ( ( v1_relat_1 @ B ) =>
% 3.44/3.64       ( ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) =
% 3.44/3.64         ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 3.44/3.64  thf('39', plain,
% 3.44/3.64      (![X62 : $i, X63 : $i]:
% 3.44/3.64         (((k1_relat_1 @ (k6_subset_1 @ X62 @ (k7_relat_1 @ X62 @ X63)))
% 3.44/3.64            = (k6_subset_1 @ (k1_relat_1 @ X62) @ X63))
% 3.44/3.64          | ~ (v1_relat_1 @ X62))),
% 3.44/3.64      inference('cnf', [status(esa)], [t212_relat_1])).
% 3.44/3.64  thf(redefinition_k6_subset_1, axiom,
% 3.44/3.64    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 3.44/3.64  thf('40', plain,
% 3.44/3.64      (![X40 : $i, X41 : $i]:
% 3.44/3.64         ((k6_subset_1 @ X40 @ X41) = (k4_xboole_0 @ X40 @ X41))),
% 3.44/3.64      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 3.44/3.64  thf('41', plain,
% 3.44/3.64      (![X40 : $i, X41 : $i]:
% 3.44/3.64         ((k6_subset_1 @ X40 @ X41) = (k4_xboole_0 @ X40 @ X41))),
% 3.44/3.64      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 3.44/3.64  thf('42', plain,
% 3.44/3.64      (![X62 : $i, X63 : $i]:
% 3.44/3.64         (((k1_relat_1 @ (k4_xboole_0 @ X62 @ (k7_relat_1 @ X62 @ X63)))
% 3.44/3.64            = (k4_xboole_0 @ (k1_relat_1 @ X62) @ X63))
% 3.44/3.64          | ~ (v1_relat_1 @ X62))),
% 3.44/3.64      inference('demod', [status(thm)], ['39', '40', '41'])).
% 3.44/3.64  thf('43', plain,
% 3.44/3.64      (![X0 : $i, X1 : $i]:
% 3.44/3.64         (((k1_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 3.44/3.64            = (k4_xboole_0 @ (k1_relat_1 @ X1) @ 
% 3.44/3.64               (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 3.44/3.64          | ~ (v1_relat_1 @ X1)
% 3.44/3.64          | ~ (v1_relat_1 @ X1))),
% 3.44/3.64      inference('sup+', [status(thm)], ['38', '42'])).
% 3.44/3.64  thf('44', plain,
% 3.44/3.64      (![X0 : $i, X1 : $i]:
% 3.44/3.64         (~ (v1_relat_1 @ X1)
% 3.44/3.64          | ((k1_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 3.44/3.64              = (k4_xboole_0 @ (k1_relat_1 @ X1) @ 
% 3.44/3.64                 (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))))),
% 3.44/3.64      inference('simplify', [status(thm)], ['43'])).
% 3.44/3.64  thf(t213_relat_1, conjecture,
% 3.44/3.64    (![A:$i,B:$i]:
% 3.44/3.64     ( ( v1_relat_1 @ B ) =>
% 3.44/3.64       ( ( k6_subset_1 @
% 3.44/3.64           ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) ) =
% 3.44/3.64         ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ))).
% 3.44/3.64  thf(zf_stmt_0, negated_conjecture,
% 3.44/3.64    (~( ![A:$i,B:$i]:
% 3.44/3.64        ( ( v1_relat_1 @ B ) =>
% 3.44/3.64          ( ( k6_subset_1 @
% 3.44/3.64              ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) ) =
% 3.44/3.64            ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ) )),
% 3.44/3.64    inference('cnf.neg', [status(esa)], [t213_relat_1])).
% 3.44/3.64  thf('45', plain,
% 3.44/3.64      (((k6_subset_1 @ (k1_relat_1 @ sk_B) @ 
% 3.44/3.64         (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 3.44/3.64         != (k1_relat_1 @ (k6_subset_1 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 3.44/3.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.64  thf('46', plain,
% 3.44/3.64      (![X40 : $i, X41 : $i]:
% 3.44/3.64         ((k6_subset_1 @ X40 @ X41) = (k4_xboole_0 @ X40 @ X41))),
% 3.44/3.64      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 3.44/3.64  thf('47', plain,
% 3.44/3.64      (![X40 : $i, X41 : $i]:
% 3.44/3.64         ((k6_subset_1 @ X40 @ X41) = (k4_xboole_0 @ X40 @ X41))),
% 3.44/3.64      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 3.44/3.64  thf('48', plain,
% 3.44/3.64      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 3.44/3.64         (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 3.44/3.64         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 3.44/3.64      inference('demod', [status(thm)], ['45', '46', '47'])).
% 3.44/3.64  thf('49', plain,
% 3.44/3.64      ((((k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A)))
% 3.44/3.64          != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))
% 3.44/3.64        | ~ (v1_relat_1 @ sk_B))),
% 3.44/3.64      inference('sup-', [status(thm)], ['44', '48'])).
% 3.44/3.64  thf('50', plain, ((v1_relat_1 @ sk_B)),
% 3.44/3.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.44/3.64  thf('51', plain,
% 3.44/3.64      (((k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A)))
% 3.44/3.64         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 3.44/3.64      inference('demod', [status(thm)], ['49', '50'])).
% 3.44/3.64  thf('52', plain, ($false), inference('simplify', [status(thm)], ['51'])).
% 3.44/3.64  
% 3.44/3.64  % SZS output end Refutation
% 3.44/3.64  
% 3.44/3.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
