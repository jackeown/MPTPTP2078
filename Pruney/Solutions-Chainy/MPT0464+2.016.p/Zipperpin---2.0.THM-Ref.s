%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9ZA9jiRnP1

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:10 EST 2020

% Result     : Theorem 37.70s
% Output     : Refutation 37.70s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 213 expanded)
%              Number of leaves         :   36 (  83 expanded)
%              Depth                    :   18
%              Number of atoms          : 1073 (1701 expanded)
%              Number of equality atoms :   61 ( 102 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('0',plain,(
    ! [X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X2 ) @ X1 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X47: $i,X49: $i] :
      ( ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X49 ) )
      | ~ ( r1_tarski @ X47 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('3',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ X53 ) )
      | ( v1_relat_1 @ X52 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('5',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k2_enumset1 @ X25 @ X25 @ X26 @ X27 )
      = ( k1_enumset1 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_enumset1 @ X23 @ X23 @ X24 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('9',plain,(
    ! [X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X2 ) @ X1 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( r2_hidden @ X41 @ X40 )
      | ~ ( r1_tarski @ ( k2_tarski @ X39 @ X41 ) @ X40 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('14',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( r2_hidden @ X39 @ X40 )
      | ~ ( r1_tarski @ ( k2_tarski @ X39 @ X41 ) @ X40 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X39: $i,X41: $i,X42: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X39 @ X41 ) @ X42 )
      | ~ ( r2_hidden @ X41 @ X42 )
      | ~ ( r2_hidden @ X39 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X2 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','18'])).

thf(t7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('20',plain,(
    ! [X50: $i,X51: $i] :
      ( ( X50 = k1_xboole_0 )
      | ~ ( r1_tarski @ X50 @ X51 )
      | ( r1_tarski @ ( k1_setfam_1 @ X51 ) @ ( k1_setfam_1 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t7_setfam_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      | ( ( k2_tarski @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k2_enumset1 @ X25 @ X25 @ X26 @ X27 )
      = ( k1_enumset1 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('23',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_enumset1 @ X23 @ X23 @ X24 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X45 @ X46 ) )
      = ( k3_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X45 @ X46 ) )
      = ( k3_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( ( k2_tarski @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('30',plain,(
    ! [X22: $i] :
      ( ( k2_tarski @ X22 @ X22 )
      = ( k1_tarski @ X22 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('31',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k2_enumset1 @ X18 @ X19 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k2_tarski @ X18 @ X19 ) @ ( k2_tarski @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('33',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X43 ) @ X44 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['28','35'])).

thf('37',plain,(
    ! [X47: $i,X49: $i] :
      ( ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X49 ) )
      | ~ ( r1_tarski @ X47 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ X53 ) )
      | ( v1_relat_1 @ X52 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','40'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('42',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k3_enumset1 @ X28 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_enumset1 @ X28 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('46',plain,(
    ! [X39: $i,X41: $i,X42: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X39 @ X41 ) @ X42 )
      | ~ ( r2_hidden @ X41 @ X42 )
      | ~ ( r2_hidden @ X39 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X2 @ X0 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X0 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X22: $i] :
      ( ( k2_tarski @ X22 @ X22 )
      = ( k1_tarski @ X22 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','51'])).

thf('53',plain,(
    ! [X50: $i,X51: $i] :
      ( ( X50 = k1_xboole_0 )
      | ~ ( r1_tarski @ X50 @ X51 )
      | ( r1_tarski @ ( k1_setfam_1 @ X51 ) @ ( k1_setfam_1 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t7_setfam_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ ( k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 ) ) @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k3_enumset1 @ X28 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_enumset1 @ X28 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X22: $i] :
      ( ( k2_tarski @ X22 @ X22 )
      = ( k1_tarski @ X22 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('59',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X45 @ X46 ) )
      = ( k3_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['54','57','62'])).

thf('64',plain,(
    ! [X22: $i] :
      ( ( k2_tarski @ X22 @ X22 )
      = ( k1_tarski @ X22 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('65',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X37 @ X38 ) )
      = ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X43 ) @ X44 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ ( k1_tarski @ X0 ) ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X22: $i] :
      ( ( k2_tarski @ X22 @ X22 )
      = ( k1_tarski @ X22 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('70',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k2_enumset1 @ X18 @ X19 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k2_tarski @ X18 @ X19 ) @ ( k2_tarski @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k1_tarski @ ( k2_tarski @ X1 @ X0 ) ) )
      = ( k2_enumset1 @ X1 @ X0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ ( k1_tarski @ X0 ) ) )
      = ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_enumset1 @ X23 @ X23 @ X24 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('75',plain,(
    ! [X22: $i] :
      ( ( k2_tarski @ X22 @ X22 )
      = ( k1_tarski @ X22 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k2_enumset1 @ X25 @ X25 @ X26 @ X27 )
      = ( k1_enumset1 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ ( k1_tarski @ X0 ) ) )
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['73','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('simplify_reflect-',[status(thm)],['63','80'])).

thf(t48_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( r1_tarski @ A @ B )
               => ( r1_tarski @ ( k5_relat_1 @ C @ A ) @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) )).

thf('82',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ~ ( v1_relat_1 @ X54 )
      | ~ ( r1_tarski @ X55 @ X54 )
      | ( r1_tarski @ ( k5_relat_1 @ X56 @ X55 ) @ ( k5_relat_1 @ X56 @ X54 ) )
      | ~ ( v1_relat_1 @ X56 )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t48_relat_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['41','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('87',plain,(
    ! [X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X2 ) @ X1 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('88',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ~ ( v1_relat_1 @ X54 )
      | ~ ( r1_tarski @ X55 @ X54 )
      | ( r1_tarski @ ( k5_relat_1 @ X56 @ X55 ) @ ( k5_relat_1 @ X56 @ X54 ) )
      | ~ ( v1_relat_1 @ X56 )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t48_relat_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('92',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ X5 )
      | ( r1_tarski @ X3 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ~ ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['85','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf(t52_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( r1_tarski @ ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ! [C: $i] :
                ( ( v1_relat_1 @ C )
               => ( r1_tarski @ ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_relat_1])).

thf('96',plain,(
    ~ ( r1_tarski @ ( k5_relat_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    $false ),
    inference(demod,[status(thm)],['97','98','99','100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9ZA9jiRnP1
% 0.16/0.38  % Computer   : n023.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 11:33:06 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 37.70/37.97  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 37.70/37.97  % Solved by: fo/fo7.sh
% 37.70/37.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 37.70/37.97  % done 28745 iterations in 37.472s
% 37.70/37.97  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 37.70/37.97  % SZS output start Refutation
% 37.70/37.97  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 37.70/37.97  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 37.70/37.97  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 37.70/37.97  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 37.70/37.97  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 37.70/37.97  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 37.70/37.97  thf(sk_B_type, type, sk_B: $i).
% 37.70/37.97  thf(sk_A_type, type, sk_A: $i).
% 37.70/37.97  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 37.70/37.97  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 37.70/37.97  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 37.70/37.97  thf(sk_C_type, type, sk_C: $i).
% 37.70/37.97  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 37.70/37.97  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 37.70/37.97  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 37.70/37.97  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 37.70/37.97  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 37.70/37.97  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 37.70/37.97  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 37.70/37.97  thf(t17_xboole_1, axiom,
% 37.70/37.97    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 37.70/37.97  thf('0', plain,
% 37.70/37.97      (![X1 : $i, X2 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X2) @ X1)),
% 37.70/37.97      inference('cnf', [status(esa)], [t17_xboole_1])).
% 37.70/37.97  thf(t3_subset, axiom,
% 37.70/37.97    (![A:$i,B:$i]:
% 37.70/37.97     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 37.70/37.97  thf('1', plain,
% 37.70/37.97      (![X47 : $i, X49 : $i]:
% 37.70/37.97         ((m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X49)) | ~ (r1_tarski @ X47 @ X49))),
% 37.70/37.97      inference('cnf', [status(esa)], [t3_subset])).
% 37.70/37.97  thf('2', plain,
% 37.70/37.97      (![X0 : $i, X1 : $i]:
% 37.70/37.97         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 37.70/37.97      inference('sup-', [status(thm)], ['0', '1'])).
% 37.70/37.97  thf(cc2_relat_1, axiom,
% 37.70/37.97    (![A:$i]:
% 37.70/37.97     ( ( v1_relat_1 @ A ) =>
% 37.70/37.97       ( ![B:$i]:
% 37.70/37.97         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 37.70/37.97  thf('3', plain,
% 37.70/37.97      (![X52 : $i, X53 : $i]:
% 37.70/37.97         (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ X53))
% 37.70/37.97          | (v1_relat_1 @ X52)
% 37.70/37.97          | ~ (v1_relat_1 @ X53))),
% 37.70/37.97      inference('cnf', [status(esa)], [cc2_relat_1])).
% 37.70/37.97  thf('4', plain,
% 37.70/37.97      (![X0 : $i, X1 : $i]:
% 37.70/37.97         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 37.70/37.97      inference('sup-', [status(thm)], ['2', '3'])).
% 37.70/37.97  thf(t71_enumset1, axiom,
% 37.70/37.97    (![A:$i,B:$i,C:$i]:
% 37.70/37.97     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 37.70/37.97  thf('5', plain,
% 37.70/37.97      (![X25 : $i, X26 : $i, X27 : $i]:
% 37.70/37.97         ((k2_enumset1 @ X25 @ X25 @ X26 @ X27)
% 37.70/37.97           = (k1_enumset1 @ X25 @ X26 @ X27))),
% 37.70/37.97      inference('cnf', [status(esa)], [t71_enumset1])).
% 37.70/37.97  thf(t70_enumset1, axiom,
% 37.70/37.97    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 37.70/37.97  thf('6', plain,
% 37.70/37.97      (![X23 : $i, X24 : $i]:
% 37.70/37.97         ((k1_enumset1 @ X23 @ X23 @ X24) = (k2_tarski @ X23 @ X24))),
% 37.70/37.97      inference('cnf', [status(esa)], [t70_enumset1])).
% 37.70/37.97  thf('7', plain,
% 37.70/37.97      (![X0 : $i, X1 : $i]:
% 37.70/37.97         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 37.70/37.97      inference('sup+', [status(thm)], ['5', '6'])).
% 37.70/37.97  thf(idempotence_k3_xboole_0, axiom,
% 37.70/37.97    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 37.70/37.97  thf('8', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 37.70/37.97      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 37.70/37.97  thf('9', plain,
% 37.70/37.97      (![X1 : $i, X2 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X2) @ X1)),
% 37.70/37.97      inference('cnf', [status(esa)], [t17_xboole_1])).
% 37.70/37.97  thf('10', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 37.70/37.97      inference('sup+', [status(thm)], ['8', '9'])).
% 37.70/37.97  thf(t38_zfmisc_1, axiom,
% 37.70/37.97    (![A:$i,B:$i,C:$i]:
% 37.70/37.97     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 37.70/37.97       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 37.70/37.97  thf('11', plain,
% 37.70/37.97      (![X39 : $i, X40 : $i, X41 : $i]:
% 37.70/37.97         ((r2_hidden @ X41 @ X40)
% 37.70/37.97          | ~ (r1_tarski @ (k2_tarski @ X39 @ X41) @ X40))),
% 37.70/37.97      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 37.70/37.97  thf('12', plain,
% 37.70/37.97      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 37.70/37.97      inference('sup-', [status(thm)], ['10', '11'])).
% 37.70/37.97  thf('13', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 37.70/37.97      inference('sup+', [status(thm)], ['8', '9'])).
% 37.70/37.97  thf('14', plain,
% 37.70/37.97      (![X39 : $i, X40 : $i, X41 : $i]:
% 37.70/37.97         ((r2_hidden @ X39 @ X40)
% 37.70/37.97          | ~ (r1_tarski @ (k2_tarski @ X39 @ X41) @ X40))),
% 37.70/37.97      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 37.70/37.97  thf('15', plain,
% 37.70/37.97      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 37.70/37.97      inference('sup-', [status(thm)], ['13', '14'])).
% 37.70/37.97  thf('16', plain,
% 37.70/37.97      (![X39 : $i, X41 : $i, X42 : $i]:
% 37.70/37.97         ((r1_tarski @ (k2_tarski @ X39 @ X41) @ X42)
% 37.70/37.97          | ~ (r2_hidden @ X41 @ X42)
% 37.70/37.97          | ~ (r2_hidden @ X39 @ X42))),
% 37.70/37.97      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 37.70/37.97  thf('17', plain,
% 37.70/37.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.70/37.97         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 37.70/37.97          | (r1_tarski @ (k2_tarski @ X2 @ X1) @ (k2_tarski @ X1 @ X0)))),
% 37.70/37.97      inference('sup-', [status(thm)], ['15', '16'])).
% 37.70/37.97  thf('18', plain,
% 37.70/37.97      (![X0 : $i, X1 : $i]:
% 37.70/37.97         (r1_tarski @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))),
% 37.70/37.97      inference('sup-', [status(thm)], ['12', '17'])).
% 37.70/37.97  thf('19', plain,
% 37.70/37.97      (![X0 : $i, X1 : $i]:
% 37.70/37.97         (r1_tarski @ (k2_tarski @ X0 @ X1) @ (k2_enumset1 @ X1 @ X1 @ X1 @ X0))),
% 37.70/37.97      inference('sup+', [status(thm)], ['7', '18'])).
% 37.70/37.97  thf(t7_setfam_1, axiom,
% 37.70/37.97    (![A:$i,B:$i]:
% 37.70/37.97     ( ( r1_tarski @ A @ B ) =>
% 37.70/37.97       ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 37.70/37.97         ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ))).
% 37.70/37.97  thf('20', plain,
% 37.70/37.97      (![X50 : $i, X51 : $i]:
% 37.70/37.97         (((X50) = (k1_xboole_0))
% 37.70/37.97          | ~ (r1_tarski @ X50 @ X51)
% 37.70/37.97          | (r1_tarski @ (k1_setfam_1 @ X51) @ (k1_setfam_1 @ X50)))),
% 37.70/37.97      inference('cnf', [status(esa)], [t7_setfam_1])).
% 37.70/37.97  thf('21', plain,
% 37.70/37.97      (![X0 : $i, X1 : $i]:
% 37.70/37.97         ((r1_tarski @ (k1_setfam_1 @ (k2_enumset1 @ X1 @ X1 @ X1 @ X0)) @ 
% 37.70/37.97           (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 37.70/37.97          | ((k2_tarski @ X0 @ X1) = (k1_xboole_0)))),
% 37.70/37.97      inference('sup-', [status(thm)], ['19', '20'])).
% 37.70/37.97  thf('22', plain,
% 37.70/37.97      (![X25 : $i, X26 : $i, X27 : $i]:
% 37.70/37.97         ((k2_enumset1 @ X25 @ X25 @ X26 @ X27)
% 37.70/37.97           = (k1_enumset1 @ X25 @ X26 @ X27))),
% 37.70/37.97      inference('cnf', [status(esa)], [t71_enumset1])).
% 37.70/37.97  thf('23', plain,
% 37.70/37.97      (![X23 : $i, X24 : $i]:
% 37.70/37.97         ((k1_enumset1 @ X23 @ X23 @ X24) = (k2_tarski @ X23 @ X24))),
% 37.70/37.97      inference('cnf', [status(esa)], [t70_enumset1])).
% 37.70/37.97  thf(t12_setfam_1, axiom,
% 37.70/37.97    (![A:$i,B:$i]:
% 37.70/37.97     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 37.70/37.97  thf('24', plain,
% 37.70/37.97      (![X45 : $i, X46 : $i]:
% 37.70/37.97         ((k1_setfam_1 @ (k2_tarski @ X45 @ X46)) = (k3_xboole_0 @ X45 @ X46))),
% 37.70/37.97      inference('cnf', [status(esa)], [t12_setfam_1])).
% 37.70/37.97  thf('25', plain,
% 37.70/37.97      (![X0 : $i, X1 : $i]:
% 37.70/37.97         ((k1_setfam_1 @ (k1_enumset1 @ X1 @ X1 @ X0))
% 37.70/37.97           = (k3_xboole_0 @ X1 @ X0))),
% 37.70/37.97      inference('sup+', [status(thm)], ['23', '24'])).
% 37.70/37.97  thf('26', plain,
% 37.70/37.97      (![X0 : $i, X1 : $i]:
% 37.70/37.97         ((k1_setfam_1 @ (k2_enumset1 @ X1 @ X1 @ X1 @ X0))
% 37.70/37.97           = (k3_xboole_0 @ X1 @ X0))),
% 37.70/37.97      inference('sup+', [status(thm)], ['22', '25'])).
% 37.70/37.97  thf('27', plain,
% 37.70/37.97      (![X45 : $i, X46 : $i]:
% 37.70/37.97         ((k1_setfam_1 @ (k2_tarski @ X45 @ X46)) = (k3_xboole_0 @ X45 @ X46))),
% 37.70/37.97      inference('cnf', [status(esa)], [t12_setfam_1])).
% 37.70/37.97  thf('28', plain,
% 37.70/37.97      (![X0 : $i, X1 : $i]:
% 37.70/37.97         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 37.70/37.97          | ((k2_tarski @ X0 @ X1) = (k1_xboole_0)))),
% 37.70/37.97      inference('demod', [status(thm)], ['21', '26', '27'])).
% 37.70/37.97  thf('29', plain,
% 37.70/37.97      (![X0 : $i, X1 : $i]:
% 37.70/37.97         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 37.70/37.97      inference('sup+', [status(thm)], ['5', '6'])).
% 37.70/37.97  thf(t69_enumset1, axiom,
% 37.70/37.97    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 37.70/37.97  thf('30', plain,
% 37.70/37.97      (![X22 : $i]: ((k2_tarski @ X22 @ X22) = (k1_tarski @ X22))),
% 37.70/37.97      inference('cnf', [status(esa)], [t69_enumset1])).
% 37.70/37.97  thf(l53_enumset1, axiom,
% 37.70/37.97    (![A:$i,B:$i,C:$i,D:$i]:
% 37.70/37.97     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 37.70/37.97       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 37.70/37.97  thf('31', plain,
% 37.70/37.97      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 37.70/37.97         ((k2_enumset1 @ X18 @ X19 @ X20 @ X21)
% 37.70/37.97           = (k2_xboole_0 @ (k2_tarski @ X18 @ X19) @ (k2_tarski @ X20 @ X21)))),
% 37.70/37.97      inference('cnf', [status(esa)], [l53_enumset1])).
% 37.70/37.97  thf('32', plain,
% 37.70/37.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.70/37.97         ((k2_enumset1 @ X0 @ X0 @ X2 @ X1)
% 37.70/37.97           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 37.70/37.97      inference('sup+', [status(thm)], ['30', '31'])).
% 37.70/37.97  thf(t49_zfmisc_1, axiom,
% 37.70/37.97    (![A:$i,B:$i]:
% 37.70/37.97     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 37.70/37.97  thf('33', plain,
% 37.70/37.97      (![X43 : $i, X44 : $i]:
% 37.70/37.97         ((k2_xboole_0 @ (k1_tarski @ X43) @ X44) != (k1_xboole_0))),
% 37.70/37.97      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 37.70/37.97  thf('34', plain,
% 37.70/37.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.70/37.97         ((k2_enumset1 @ X2 @ X2 @ X1 @ X0) != (k1_xboole_0))),
% 37.70/37.97      inference('sup-', [status(thm)], ['32', '33'])).
% 37.70/37.97  thf('35', plain,
% 37.70/37.97      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) != (k1_xboole_0))),
% 37.70/37.97      inference('sup-', [status(thm)], ['29', '34'])).
% 37.70/37.97  thf('36', plain,
% 37.70/37.97      (![X0 : $i, X1 : $i]:
% 37.70/37.97         (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1))),
% 37.70/37.97      inference('simplify_reflect-', [status(thm)], ['28', '35'])).
% 37.70/37.97  thf('37', plain,
% 37.70/37.97      (![X47 : $i, X49 : $i]:
% 37.70/37.97         ((m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X49)) | ~ (r1_tarski @ X47 @ X49))),
% 37.70/37.97      inference('cnf', [status(esa)], [t3_subset])).
% 37.70/37.97  thf('38', plain,
% 37.70/37.97      (![X0 : $i, X1 : $i]:
% 37.70/37.97         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ 
% 37.70/37.97          (k1_zfmisc_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 37.70/37.97      inference('sup-', [status(thm)], ['36', '37'])).
% 37.70/37.97  thf('39', plain,
% 37.70/37.97      (![X52 : $i, X53 : $i]:
% 37.70/37.97         (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ X53))
% 37.70/37.97          | (v1_relat_1 @ X52)
% 37.70/37.97          | ~ (v1_relat_1 @ X53))),
% 37.70/37.97      inference('cnf', [status(esa)], [cc2_relat_1])).
% 37.70/37.97  thf('40', plain,
% 37.70/37.97      (![X0 : $i, X1 : $i]:
% 37.70/37.97         (~ (v1_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 37.70/37.97          | (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 37.70/37.97      inference('sup-', [status(thm)], ['38', '39'])).
% 37.70/37.97  thf('41', plain,
% 37.70/37.97      (![X0 : $i, X1 : $i]:
% 37.70/37.97         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 37.70/37.97      inference('sup-', [status(thm)], ['4', '40'])).
% 37.70/37.97  thf(t72_enumset1, axiom,
% 37.70/37.97    (![A:$i,B:$i,C:$i,D:$i]:
% 37.70/37.97     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 37.70/37.97  thf('42', plain,
% 37.70/37.97      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 37.70/37.97         ((k3_enumset1 @ X28 @ X28 @ X29 @ X30 @ X31)
% 37.70/37.97           = (k2_enumset1 @ X28 @ X29 @ X30 @ X31))),
% 37.70/37.97      inference('cnf', [status(esa)], [t72_enumset1])).
% 37.70/37.97  thf('43', plain,
% 37.70/37.97      (![X0 : $i, X1 : $i]:
% 37.70/37.97         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 37.70/37.97      inference('sup+', [status(thm)], ['5', '6'])).
% 37.70/37.97  thf('44', plain,
% 37.70/37.97      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 37.70/37.97      inference('sup-', [status(thm)], ['10', '11'])).
% 37.70/37.97  thf('45', plain,
% 37.70/37.97      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 37.70/37.97      inference('sup-', [status(thm)], ['10', '11'])).
% 37.70/37.97  thf('46', plain,
% 37.70/37.97      (![X39 : $i, X41 : $i, X42 : $i]:
% 37.70/37.97         ((r1_tarski @ (k2_tarski @ X39 @ X41) @ X42)
% 37.70/37.97          | ~ (r2_hidden @ X41 @ X42)
% 37.70/37.97          | ~ (r2_hidden @ X39 @ X42))),
% 37.70/37.97      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 37.70/37.97  thf('47', plain,
% 37.70/37.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.70/37.97         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 37.70/37.97          | (r1_tarski @ (k2_tarski @ X2 @ X0) @ (k2_tarski @ X1 @ X0)))),
% 37.70/37.97      inference('sup-', [status(thm)], ['45', '46'])).
% 37.70/37.97  thf('48', plain,
% 37.70/37.97      (![X0 : $i, X1 : $i]:
% 37.70/37.97         (r1_tarski @ (k2_tarski @ X0 @ X0) @ (k2_tarski @ X1 @ X0))),
% 37.70/37.97      inference('sup-', [status(thm)], ['44', '47'])).
% 37.70/37.97  thf('49', plain,
% 37.70/37.97      (![X22 : $i]: ((k2_tarski @ X22 @ X22) = (k1_tarski @ X22))),
% 37.70/37.97      inference('cnf', [status(esa)], [t69_enumset1])).
% 37.70/37.97  thf('50', plain,
% 37.70/37.97      (![X0 : $i, X1 : $i]:
% 37.70/37.97         (r1_tarski @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))),
% 37.70/37.97      inference('demod', [status(thm)], ['48', '49'])).
% 37.70/37.97  thf('51', plain,
% 37.70/37.97      (![X0 : $i, X1 : $i]:
% 37.70/37.97         (r1_tarski @ (k1_tarski @ X0) @ (k2_enumset1 @ X1 @ X1 @ X1 @ X0))),
% 37.70/37.97      inference('sup+', [status(thm)], ['43', '50'])).
% 37.70/37.97  thf('52', plain,
% 37.70/37.97      (![X0 : $i, X1 : $i]:
% 37.70/37.97         (r1_tarski @ (k1_tarski @ X0) @ (k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0))),
% 37.70/37.97      inference('sup+', [status(thm)], ['42', '51'])).
% 37.70/37.97  thf('53', plain,
% 37.70/37.97      (![X50 : $i, X51 : $i]:
% 37.70/37.97         (((X50) = (k1_xboole_0))
% 37.70/37.97          | ~ (r1_tarski @ X50 @ X51)
% 37.70/37.97          | (r1_tarski @ (k1_setfam_1 @ X51) @ (k1_setfam_1 @ X50)))),
% 37.70/37.97      inference('cnf', [status(esa)], [t7_setfam_1])).
% 37.70/37.97  thf('54', plain,
% 37.70/37.97      (![X0 : $i, X1 : $i]:
% 37.70/37.97         ((r1_tarski @ 
% 37.70/37.97           (k1_setfam_1 @ (k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0)) @ 
% 37.70/37.97           (k1_setfam_1 @ (k1_tarski @ X0)))
% 37.70/37.97          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 37.70/37.97      inference('sup-', [status(thm)], ['52', '53'])).
% 37.70/37.97  thf('55', plain,
% 37.70/37.97      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 37.70/37.97         ((k3_enumset1 @ X28 @ X28 @ X29 @ X30 @ X31)
% 37.70/37.97           = (k2_enumset1 @ X28 @ X29 @ X30 @ X31))),
% 37.70/37.97      inference('cnf', [status(esa)], [t72_enumset1])).
% 37.70/37.97  thf('56', plain,
% 37.70/37.97      (![X0 : $i, X1 : $i]:
% 37.70/37.97         ((k1_setfam_1 @ (k2_enumset1 @ X1 @ X1 @ X1 @ X0))
% 37.70/37.97           = (k3_xboole_0 @ X1 @ X0))),
% 37.70/37.97      inference('sup+', [status(thm)], ['22', '25'])).
% 37.70/37.97  thf('57', plain,
% 37.70/37.97      (![X0 : $i, X1 : $i]:
% 37.70/37.97         ((k1_setfam_1 @ (k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0))
% 37.70/37.97           = (k3_xboole_0 @ X1 @ X0))),
% 37.70/37.97      inference('sup+', [status(thm)], ['55', '56'])).
% 37.70/37.97  thf('58', plain,
% 37.70/37.97      (![X22 : $i]: ((k2_tarski @ X22 @ X22) = (k1_tarski @ X22))),
% 37.70/37.97      inference('cnf', [status(esa)], [t69_enumset1])).
% 37.70/37.97  thf('59', plain,
% 37.70/37.97      (![X45 : $i, X46 : $i]:
% 37.70/37.97         ((k1_setfam_1 @ (k2_tarski @ X45 @ X46)) = (k3_xboole_0 @ X45 @ X46))),
% 37.70/37.97      inference('cnf', [status(esa)], [t12_setfam_1])).
% 37.70/37.97  thf('60', plain,
% 37.70/37.97      (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 37.70/37.97      inference('sup+', [status(thm)], ['58', '59'])).
% 37.70/37.97  thf('61', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 37.70/37.97      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 37.70/37.97  thf('62', plain, (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (X0))),
% 37.70/37.97      inference('demod', [status(thm)], ['60', '61'])).
% 37.70/37.97  thf('63', plain,
% 37.70/37.97      (![X0 : $i, X1 : $i]:
% 37.70/37.97         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 37.70/37.97          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 37.70/37.97      inference('demod', [status(thm)], ['54', '57', '62'])).
% 37.70/37.97  thf('64', plain,
% 37.70/37.97      (![X22 : $i]: ((k2_tarski @ X22 @ X22) = (k1_tarski @ X22))),
% 37.70/37.97      inference('cnf', [status(esa)], [t69_enumset1])).
% 37.70/37.97  thf(l51_zfmisc_1, axiom,
% 37.70/37.97    (![A:$i,B:$i]:
% 37.70/37.97     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 37.70/37.97  thf('65', plain,
% 37.70/37.97      (![X37 : $i, X38 : $i]:
% 37.70/37.97         ((k3_tarski @ (k2_tarski @ X37 @ X38)) = (k2_xboole_0 @ X37 @ X38))),
% 37.70/37.97      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 37.70/37.97  thf('66', plain,
% 37.70/37.97      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 37.70/37.97      inference('sup+', [status(thm)], ['64', '65'])).
% 37.70/37.97  thf('67', plain,
% 37.70/37.97      (![X43 : $i, X44 : $i]:
% 37.70/37.97         ((k2_xboole_0 @ (k1_tarski @ X43) @ X44) != (k1_xboole_0))),
% 37.70/37.97      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 37.70/37.97  thf('68', plain,
% 37.70/37.97      (![X0 : $i]:
% 37.70/37.97         ((k3_tarski @ (k1_tarski @ (k1_tarski @ X0))) != (k1_xboole_0))),
% 37.70/37.97      inference('sup-', [status(thm)], ['66', '67'])).
% 37.70/37.97  thf('69', plain,
% 37.70/37.97      (![X22 : $i]: ((k2_tarski @ X22 @ X22) = (k1_tarski @ X22))),
% 37.70/37.97      inference('cnf', [status(esa)], [t69_enumset1])).
% 37.70/37.97  thf('70', plain,
% 37.70/37.97      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 37.70/37.97         ((k2_enumset1 @ X18 @ X19 @ X20 @ X21)
% 37.70/37.97           = (k2_xboole_0 @ (k2_tarski @ X18 @ X19) @ (k2_tarski @ X20 @ X21)))),
% 37.70/37.97      inference('cnf', [status(esa)], [l53_enumset1])).
% 37.70/37.97  thf('71', plain,
% 37.70/37.97      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 37.70/37.97      inference('sup+', [status(thm)], ['64', '65'])).
% 37.70/37.97  thf('72', plain,
% 37.70/37.97      (![X0 : $i, X1 : $i]:
% 37.70/37.97         ((k3_tarski @ (k1_tarski @ (k2_tarski @ X1 @ X0)))
% 37.70/37.97           = (k2_enumset1 @ X1 @ X0 @ X1 @ X0))),
% 37.70/37.97      inference('sup+', [status(thm)], ['70', '71'])).
% 37.70/37.97  thf('73', plain,
% 37.70/37.97      (![X0 : $i]:
% 37.70/37.97         ((k3_tarski @ (k1_tarski @ (k1_tarski @ X0)))
% 37.70/37.97           = (k2_enumset1 @ X0 @ X0 @ X0 @ X0))),
% 37.70/37.97      inference('sup+', [status(thm)], ['69', '72'])).
% 37.70/37.97  thf('74', plain,
% 37.70/37.97      (![X23 : $i, X24 : $i]:
% 37.70/37.97         ((k1_enumset1 @ X23 @ X23 @ X24) = (k2_tarski @ X23 @ X24))),
% 37.70/37.97      inference('cnf', [status(esa)], [t70_enumset1])).
% 37.70/37.97  thf('75', plain,
% 37.70/37.97      (![X22 : $i]: ((k2_tarski @ X22 @ X22) = (k1_tarski @ X22))),
% 37.70/37.97      inference('cnf', [status(esa)], [t69_enumset1])).
% 37.70/37.97  thf('76', plain,
% 37.70/37.97      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 37.70/37.97      inference('sup+', [status(thm)], ['74', '75'])).
% 37.70/37.97  thf('77', plain,
% 37.70/37.97      (![X25 : $i, X26 : $i, X27 : $i]:
% 37.70/37.97         ((k2_enumset1 @ X25 @ X25 @ X26 @ X27)
% 37.70/37.97           = (k1_enumset1 @ X25 @ X26 @ X27))),
% 37.70/37.97      inference('cnf', [status(esa)], [t71_enumset1])).
% 37.70/37.97  thf('78', plain,
% 37.70/37.97      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 37.70/37.97      inference('sup+', [status(thm)], ['76', '77'])).
% 37.70/37.97  thf('79', plain,
% 37.70/37.97      (![X0 : $i]:
% 37.70/37.97         ((k3_tarski @ (k1_tarski @ (k1_tarski @ X0))) = (k1_tarski @ X0))),
% 37.70/37.97      inference('demod', [status(thm)], ['73', '78'])).
% 37.70/37.97  thf('80', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 37.70/37.97      inference('demod', [status(thm)], ['68', '79'])).
% 37.70/37.97  thf('81', plain,
% 37.70/37.97      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 37.70/37.97      inference('simplify_reflect-', [status(thm)], ['63', '80'])).
% 37.70/37.97  thf(t48_relat_1, axiom,
% 37.70/37.97    (![A:$i]:
% 37.70/37.97     ( ( v1_relat_1 @ A ) =>
% 37.70/37.97       ( ![B:$i]:
% 37.70/37.97         ( ( v1_relat_1 @ B ) =>
% 37.70/37.97           ( ![C:$i]:
% 37.70/37.97             ( ( v1_relat_1 @ C ) =>
% 37.70/37.97               ( ( r1_tarski @ A @ B ) =>
% 37.70/37.97                 ( r1_tarski @ ( k5_relat_1 @ C @ A ) @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) ) ))).
% 37.70/37.97  thf('82', plain,
% 37.70/37.97      (![X54 : $i, X55 : $i, X56 : $i]:
% 37.70/37.97         (~ (v1_relat_1 @ X54)
% 37.70/37.97          | ~ (r1_tarski @ X55 @ X54)
% 37.70/37.97          | (r1_tarski @ (k5_relat_1 @ X56 @ X55) @ (k5_relat_1 @ X56 @ X54))
% 37.70/37.97          | ~ (v1_relat_1 @ X56)
% 37.70/37.97          | ~ (v1_relat_1 @ X55))),
% 37.70/37.97      inference('cnf', [status(esa)], [t48_relat_1])).
% 37.70/37.97  thf('83', plain,
% 37.70/37.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.70/37.97         (~ (v1_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 37.70/37.97          | ~ (v1_relat_1 @ X2)
% 37.70/37.97          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 37.70/37.97             (k5_relat_1 @ X2 @ X0))
% 37.70/37.97          | ~ (v1_relat_1 @ X0))),
% 37.70/37.97      inference('sup-', [status(thm)], ['81', '82'])).
% 37.70/37.97  thf('84', plain,
% 37.70/37.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.70/37.97         (~ (v1_relat_1 @ X0)
% 37.70/37.97          | ~ (v1_relat_1 @ X0)
% 37.70/37.97          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 37.70/37.97             (k5_relat_1 @ X2 @ X0))
% 37.70/37.97          | ~ (v1_relat_1 @ X2))),
% 37.70/37.97      inference('sup-', [status(thm)], ['41', '83'])).
% 37.70/37.97  thf('85', plain,
% 37.70/37.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.70/37.97         (~ (v1_relat_1 @ X2)
% 37.70/37.97          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 37.70/37.97             (k5_relat_1 @ X2 @ X0))
% 37.70/37.97          | ~ (v1_relat_1 @ X0))),
% 37.70/37.97      inference('simplify', [status(thm)], ['84'])).
% 37.70/37.97  thf('86', plain,
% 37.70/37.97      (![X0 : $i, X1 : $i]:
% 37.70/37.97         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 37.70/37.97      inference('sup-', [status(thm)], ['2', '3'])).
% 37.70/37.97  thf('87', plain,
% 37.70/37.97      (![X1 : $i, X2 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X2) @ X1)),
% 37.70/37.97      inference('cnf', [status(esa)], [t17_xboole_1])).
% 37.70/37.97  thf('88', plain,
% 37.70/37.97      (![X54 : $i, X55 : $i, X56 : $i]:
% 37.70/37.97         (~ (v1_relat_1 @ X54)
% 37.70/37.97          | ~ (r1_tarski @ X55 @ X54)
% 37.70/37.97          | (r1_tarski @ (k5_relat_1 @ X56 @ X55) @ (k5_relat_1 @ X56 @ X54))
% 37.70/37.97          | ~ (v1_relat_1 @ X56)
% 37.70/37.97          | ~ (v1_relat_1 @ X55))),
% 37.70/37.97      inference('cnf', [status(esa)], [t48_relat_1])).
% 37.70/37.97  thf('89', plain,
% 37.70/37.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.70/37.97         (~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 37.70/37.97          | ~ (v1_relat_1 @ X2)
% 37.70/37.97          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 37.70/37.97             (k5_relat_1 @ X2 @ X0))
% 37.70/37.97          | ~ (v1_relat_1 @ X0))),
% 37.70/37.97      inference('sup-', [status(thm)], ['87', '88'])).
% 37.70/37.97  thf('90', plain,
% 37.70/37.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.70/37.97         (~ (v1_relat_1 @ X1)
% 37.70/37.97          | ~ (v1_relat_1 @ X1)
% 37.70/37.97          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 37.70/37.97             (k5_relat_1 @ X2 @ X1))
% 37.70/37.97          | ~ (v1_relat_1 @ X2))),
% 37.70/37.97      inference('sup-', [status(thm)], ['86', '89'])).
% 37.70/37.97  thf('91', plain,
% 37.70/37.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.70/37.97         (~ (v1_relat_1 @ X2)
% 37.70/37.97          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 37.70/37.97             (k5_relat_1 @ X2 @ X1))
% 37.70/37.97          | ~ (v1_relat_1 @ X1))),
% 37.70/37.97      inference('simplify', [status(thm)], ['90'])).
% 37.70/37.97  thf(t19_xboole_1, axiom,
% 37.70/37.97    (![A:$i,B:$i,C:$i]:
% 37.70/37.97     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 37.70/37.97       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 37.70/37.97  thf('92', plain,
% 37.70/37.97      (![X3 : $i, X4 : $i, X5 : $i]:
% 37.70/37.97         (~ (r1_tarski @ X3 @ X4)
% 37.70/37.97          | ~ (r1_tarski @ X3 @ X5)
% 37.70/37.97          | (r1_tarski @ X3 @ (k3_xboole_0 @ X4 @ X5)))),
% 37.70/37.97      inference('cnf', [status(esa)], [t19_xboole_1])).
% 37.70/37.97  thf('93', plain,
% 37.70/37.97      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 37.70/37.97         (~ (v1_relat_1 @ X0)
% 37.70/37.97          | ~ (v1_relat_1 @ X1)
% 37.70/37.97          | (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ 
% 37.70/37.97             (k3_xboole_0 @ (k5_relat_1 @ X1 @ X0) @ X3))
% 37.70/37.97          | ~ (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ X3))),
% 37.70/37.97      inference('sup-', [status(thm)], ['91', '92'])).
% 37.70/37.97  thf('94', plain,
% 37.70/37.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.70/37.97         (~ (v1_relat_1 @ X0)
% 37.70/37.97          | ~ (v1_relat_1 @ X1)
% 37.70/37.97          | (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 37.70/37.97             (k3_xboole_0 @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0)))
% 37.70/37.97          | ~ (v1_relat_1 @ X1)
% 37.70/37.97          | ~ (v1_relat_1 @ X2))),
% 37.70/37.97      inference('sup-', [status(thm)], ['85', '93'])).
% 37.70/37.97  thf('95', plain,
% 37.70/37.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.70/37.97         (~ (v1_relat_1 @ X2)
% 37.70/37.97          | (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 37.70/37.97             (k3_xboole_0 @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0)))
% 37.70/37.97          | ~ (v1_relat_1 @ X1)
% 37.70/37.97          | ~ (v1_relat_1 @ X0))),
% 37.70/37.97      inference('simplify', [status(thm)], ['94'])).
% 37.70/37.97  thf(t52_relat_1, conjecture,
% 37.70/37.97    (![A:$i]:
% 37.70/37.97     ( ( v1_relat_1 @ A ) =>
% 37.70/37.97       ( ![B:$i]:
% 37.70/37.97         ( ( v1_relat_1 @ B ) =>
% 37.70/37.97           ( ![C:$i]:
% 37.70/37.97             ( ( v1_relat_1 @ C ) =>
% 37.70/37.97               ( r1_tarski @
% 37.70/37.97                 ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 37.70/37.97                 ( k3_xboole_0 @
% 37.70/37.97                   ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ))).
% 37.70/37.97  thf(zf_stmt_0, negated_conjecture,
% 37.70/37.97    (~( ![A:$i]:
% 37.70/37.97        ( ( v1_relat_1 @ A ) =>
% 37.70/37.97          ( ![B:$i]:
% 37.70/37.97            ( ( v1_relat_1 @ B ) =>
% 37.70/37.97              ( ![C:$i]:
% 37.70/37.97                ( ( v1_relat_1 @ C ) =>
% 37.70/37.97                  ( r1_tarski @
% 37.70/37.97                    ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 37.70/37.97                    ( k3_xboole_0 @
% 37.70/37.97                      ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ) )),
% 37.70/37.97    inference('cnf.neg', [status(esa)], [t52_relat_1])).
% 37.70/37.97  thf('96', plain,
% 37.70/37.97      (~ (r1_tarski @ (k5_relat_1 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 37.70/37.97          (k3_xboole_0 @ (k5_relat_1 @ sk_A @ sk_B) @ 
% 37.70/37.97           (k5_relat_1 @ sk_A @ sk_C)))),
% 37.70/37.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.70/37.97  thf('97', plain,
% 37.70/37.97      ((~ (v1_relat_1 @ sk_C) | ~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 37.70/37.97      inference('sup-', [status(thm)], ['95', '96'])).
% 37.70/37.97  thf('98', plain, ((v1_relat_1 @ sk_C)),
% 37.70/37.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.70/37.97  thf('99', plain, ((v1_relat_1 @ sk_A)),
% 37.70/37.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.70/37.97  thf('100', plain, ((v1_relat_1 @ sk_B)),
% 37.70/37.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.70/37.97  thf('101', plain, ($false),
% 37.70/37.97      inference('demod', [status(thm)], ['97', '98', '99', '100'])).
% 37.70/37.97  
% 37.70/37.97  % SZS output end Refutation
% 37.70/37.97  
% 37.70/37.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
