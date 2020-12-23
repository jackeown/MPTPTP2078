%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FuFZZPA2p0

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:05 EST 2020

% Result     : Theorem 3.34s
% Output     : Refutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :  454 (11132 expanded)
%              Number of leaves         :   52 (3135 expanded)
%              Depth                    :   55
%              Number of atoms          : 5063 (195044 expanded)
%              Number of equality atoms :  286 (11479 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('0',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X13 ) )
        = X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('2',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('3',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X13 ) )
        = X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('4',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('5',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('6',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X13 ) )
        = X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('7',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('8',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('9',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_funct_1 @ X9 )
        = ( k4_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['5','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['4','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ X0 )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('22',plain,(
    ! [X1: $i] :
      ( ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['2','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X13 ) )
        = X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('32',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X13 ) )
        = X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('34',plain,(
    ! [X8: $i] :
      ( ( ( k7_relat_1 @ X8 @ ( k1_relat_1 @ X8 ) )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('42',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k7_relat_1 @ X7 @ X6 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X6 ) @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('43',plain,(
    ! [X8: $i] :
      ( ( ( k7_relat_1 @ X8 @ ( k1_relat_1 @ X8 ) )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf(t36_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ C )
                = B )
              & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
              & ( v2_funct_1 @ C ) )
           => ( ( A = k1_xboole_0 )
              | ( B = k1_xboole_0 )
              | ( D
                = ( k2_funct_1 @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( ( ( k2_relset_1 @ A @ B @ C )
                  = B )
                & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
                & ( v2_funct_1 @ C ) )
             => ( ( A = k1_xboole_0 )
                | ( B = k1_xboole_0 )
                | ( D
                  = ( k2_funct_1 @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_funct_2])).

thf('44',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('45',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('46',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('49',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['47','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('56',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( X20 = X23 )
      | ~ ( r2_relset_1 @ X21 @ X22 @ X20 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','57'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('59',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('60',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('61',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['58','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ ( k6_partfun1 @ B ) )
           => ( ( k2_relset_1 @ A @ B @ C )
              = B ) ) ) ) )).

thf('64',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_2 @ X39 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( r2_relset_1 @ X40 @ X40 @ ( k1_partfun1 @ X40 @ X41 @ X41 @ X40 @ X39 @ X42 ) @ ( k6_partfun1 @ X40 ) )
      | ( ( k2_relset_1 @ X41 @ X40 @ X42 )
        = X40 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) )
      | ~ ( v1_funct_2 @ X42 @ X41 @ X40 )
      | ~ ( v1_funct_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('65',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('66',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_2 @ X39 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( r2_relset_1 @ X40 @ X40 @ ( k1_partfun1 @ X40 @ X41 @ X41 @ X40 @ X39 @ X42 ) @ ( k6_relat_1 @ X40 ) )
      | ( ( k2_relset_1 @ X41 @ X40 @ X42 )
        = X40 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) )
      | ~ ( v1_funct_2 @ X42 @ X41 @ X40 )
      | ~ ( v1_funct_1 @ X42 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['62','70'])).

thf('72',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('73',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( r2_relset_1 @ X21 @ X22 @ X20 @ X23 )
      | ( X20 != X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('74',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_relset_1 @ X21 @ X22 @ X23 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('77',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('78',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['71','75','78','79','80','81'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('83',plain,(
    ! [X5: $i] :
      ( ( ( k5_relat_1 @ X5 @ ( k6_relat_1 @ ( k2_relat_1 @ X5 ) ) )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('84',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k6_relat_1 @ sk_A ) )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('86',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('87',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_relat_1 @ sk_A ) )
    = sk_D ),
    inference(demod,[status(thm)],['84','87'])).

thf('89',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k7_relat_1 @ X7 @ X6 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X6 ) @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('90',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('92',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k6_relat_1 @ sk_A ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_D ) )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['88','94'])).

thf('96',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['85','86'])).

thf('97',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k6_relat_1 @ sk_A ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['43','98'])).

thf('100',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_relat_1 @ sk_A ) )
    = sk_D ),
    inference(demod,[status(thm)],['84','87'])).

thf('101',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['85','86'])).

thf('102',plain,
    ( sk_D
    = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,
    ( ( sk_D
      = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['42','102'])).

thf('104',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['85','86'])).

thf('105',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( sk_D
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['41','105'])).

thf('107',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['85','86'])).

thf('108',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( sk_D
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['58','61'])).

thf('111',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_2 @ D @ A @ B )
        & ( v1_funct_1 @ D ) )
     => ! [E: $i] :
          ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
            & ( v1_funct_2 @ E @ B @ C )
            & ( v1_funct_1 @ E ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ D )
                = B )
              & ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) )
           => ( ( ( v2_funct_1 @ E )
                & ( v2_funct_1 @ D ) )
              | ( ( B != k1_xboole_0 )
                & ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i] :
      ( ( zip_tseitin_1 @ C @ B )
     => ( ( C = k1_xboole_0 )
        & ( B != k1_xboole_0 ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [E: $i,D: $i] :
      ( ( zip_tseitin_0 @ E @ D )
     => ( ( v2_funct_1 @ D )
        & ( v2_funct_1 @ E ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
              & ( ( k2_relset_1 @ A @ B @ D )
                = B ) )
           => ( ( zip_tseitin_1 @ C @ B )
              | ( zip_tseitin_0 @ E @ D ) ) ) ) ) )).

thf('112',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_2 @ X47 @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ( zip_tseitin_0 @ X47 @ X50 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X51 @ X48 @ X48 @ X49 @ X50 @ X47 ) )
      | ( zip_tseitin_1 @ X49 @ X48 )
      | ( ( k2_relset_1 @ X51 @ X48 @ X50 )
       != X48 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X48 ) ) )
      | ~ ( v1_funct_2 @ X50 @ X51 @ X48 )
      | ~ ( v1_funct_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['110','116'])).

thf('118',plain,(
    ! [X12: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('119',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['117','118','119','120','121','122'])).

thf('124',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    ! [X45: $i,X46: $i] :
      ( ( X45 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('126',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X43: $i,X44: $i] :
      ( ( v2_funct_1 @ X44 )
      | ~ ( zip_tseitin_0 @ X44 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('130',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( sk_D
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['109','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_funct_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X13 ) )
        = X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('139',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('140',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('142',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['140','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['139','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['138','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X13 ) )
        = X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('152',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('153',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('155',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['153','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['152','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['151','160'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['148'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k2_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['162','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( v1_relat_1 @ ( k2_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['150','167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_relat_1 @ ( k2_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['149','169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['137','171'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k2_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X13 ) )
        = X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('175',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('176',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X13 ) )
        = X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('177',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X13 ) )
        = X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('178',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k2_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['177','180'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['181'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( v1_funct_1 @ ( k2_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['176','182'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['183'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_funct_1 @ ( k2_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['175','184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['185'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['174','186'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k2_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['187'])).

thf('189',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X13 ) )
        = X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('190',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('191',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['148'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('193',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X13 ) )
        = X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('194',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_funct_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('195',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_funct_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['195'])).

thf('197',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['192','196'])).

thf('198',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['197'])).

thf('199',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['197'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['198','199'])).

thf('201',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['191','200'])).

thf('202',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['201'])).

thf('203',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['190','202'])).

thf('204',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['203'])).

thf('205',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['189','204'])).

thf('206',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['205'])).

thf('207',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('208',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['206','207'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_relat_1 @ ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['188','208'])).

thf('210',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['209'])).

thf('211',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_relat_1 @ ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['173','210'])).

thf('212',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['211'])).

thf('213',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['136','212'])).

thf('214',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k2_funct_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['213'])).

thf('215',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['132','214'])).

thf('216',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['215'])).

thf('217',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('218',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_funct_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('219',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X13 ) )
        = X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('220',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X13 ) )
        = X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('221',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('222',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('223',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['221','222'])).

thf('224',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['220','223'])).

thf('225',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['224'])).

thf('226',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['219','225'])).

thf('227',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['226'])).

thf('228',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['218','227'])).

thf('229',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k2_funct_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['228'])).

thf('230',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['217','229'])).

thf('231',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['230'])).

thf('232',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_funct_1 @ X9 )
        = ( k4_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('233',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['231','232'])).

thf('234',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['216','233'])).

thf('235',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['234'])).

thf('236',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) ) )
      = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) ) ) ) ),
    inference('sup-',[status(thm)],['131','235'])).

thf('237',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['85','86'])).

thf('238',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['128','129'])).

thf('240',plain,
    ( sk_D
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['109','130'])).

thf('241',plain,
    ( sk_D
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['109','130'])).

thf('242',plain,
    ( sk_D
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['109','130'])).

thf('243',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_D ) )
    | ( sk_D
      = ( k4_relat_1 @ ( k2_funct_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['236','237','238','239','240','241','242'])).

thf('244',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_funct_1 @ X9 )
        = ( k4_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('246',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k2_funct_1 @ sk_D )
      = ( k4_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['244','245'])).

thf('247',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['85','86'])).

thf('248',plain,
    ( ( ( k2_funct_1 @ sk_D )
      = ( k4_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['246','247'])).

thf('249',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['128','129'])).

thf('250',plain,
    ( ( k2_funct_1 @ sk_D )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['248','249'])).

thf('251',plain,
    ( ( k2_funct_1 @ sk_D )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['248','249'])).

thf('252',plain,
    ( ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_D ) )
    | ( sk_D
      = ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['243','250','251'])).

thf('253',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
          & ( v2_funct_1 @ C ) )
       => ( ( B = k1_xboole_0 )
          | ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) )
              = ( k6_partfun1 @ A ) )
            & ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C )
              = ( k6_partfun1 @ B ) ) ) ) ) ) )).

thf('254',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( X52 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( v1_funct_2 @ X53 @ X54 @ X52 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X52 ) ) )
      | ( ( k5_relat_1 @ X53 @ ( k2_funct_1 @ X53 ) )
        = ( k6_partfun1 @ X54 ) )
      | ~ ( v2_funct_1 @ X53 )
      | ( ( k2_relset_1 @ X54 @ X52 @ X53 )
       != X52 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('255',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('256',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( X52 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( v1_funct_2 @ X53 @ X54 @ X52 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X52 ) ) )
      | ( ( k5_relat_1 @ X53 @ ( k2_funct_1 @ X53 ) )
        = ( k6_relat_1 @ X54 ) )
      | ~ ( v2_funct_1 @ X53 )
      | ( ( k2_relset_1 @ X54 @ X52 @ X53 )
       != X52 ) ) ),
    inference(demod,[status(thm)],['254','255'])).

thf('257',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['253','256'])).

thf('258',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('259',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('260',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('261',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['257','258','259','260'])).

thf('262',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['261','262'])).

thf('264',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['71','75','78','79','80','81'])).

thf('265',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['263','264'])).

thf('266',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['265'])).

thf('267',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['128','129'])).

thf('268',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['266','267'])).

thf('269',plain,
    ( ( k2_funct_1 @ sk_D )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['248','249'])).

thf('270',plain,
    ( ( k5_relat_1 @ sk_D @ ( k4_relat_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['268','269'])).

thf('271',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('272',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('273',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( ( k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35 )
        = ( k5_relat_1 @ X32 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('274',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['272','273'])).

thf('275',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('276',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['274','275'])).

thf('277',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['271','276'])).

thf('278',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('279',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['58','61'])).

thf('280',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['277','278','279'])).

thf('281',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('282',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['280','281'])).

thf('283',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('284',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('285',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['283','284'])).

thf('286',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['85','86'])).

thf('287',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['282','285','286'])).

thf('288',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k4_relat_1 @ sk_D ) )
      = ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['270','287'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('289',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('290',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('291',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['85','86'])).

thf('292',plain,(
    ! [X1: $i] :
      ( ( ( k2_relat_1 @ X1 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('293',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['291','292'])).

thf('294',plain,(
    ! [X8: $i] :
      ( ( ( k7_relat_1 @ X8 @ ( k1_relat_1 @ X8 ) )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('295',plain,
    ( ( ( k7_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) )
      = ( k4_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['293','294'])).

thf('296',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k7_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) )
      = ( k4_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['290','295'])).

thf('297',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['85','86'])).

thf('298',plain,
    ( ( k7_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['296','297'])).

thf('299',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['71','75','78','79','80','81'])).

thf('300',plain,
    ( ( k7_relat_1 @ ( k4_relat_1 @ sk_D ) @ sk_A )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['298','299'])).

thf('301',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k7_relat_1 @ X7 @ X6 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X6 ) @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('302',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('303',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( X52 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( v1_funct_2 @ X53 @ X54 @ X52 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X52 ) ) )
      | ( ( k5_relat_1 @ X53 @ ( k2_funct_1 @ X53 ) )
        = ( k6_relat_1 @ X54 ) )
      | ~ ( v2_funct_1 @ X53 )
      | ( ( k2_relset_1 @ X54 @ X52 @ X53 )
       != X52 ) ) ),
    inference(demod,[status(thm)],['254','255'])).

thf('304',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['302','303'])).

thf('305',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('306',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('307',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('308',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_funct_1 @ X9 )
        = ( k4_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('309',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['307','308'])).

thf('310',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['283','284'])).

thf('311',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('312',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['309','310','311'])).

thf('313',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('314',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('315',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['304','305','306','312','313','314'])).

thf('316',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['315'])).

thf('317',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('318',plain,
    ( ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['316','317'])).

thf('319',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('320',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( X52 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( v1_funct_2 @ X53 @ X54 @ X52 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X52 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X53 ) @ X53 )
        = ( k6_partfun1 @ X52 ) )
      | ~ ( v2_funct_1 @ X53 )
      | ( ( k2_relset_1 @ X54 @ X52 @ X53 )
       != X52 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('321',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('322',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( X52 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( v1_funct_2 @ X53 @ X54 @ X52 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X52 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X53 ) @ X53 )
        = ( k6_relat_1 @ X52 ) )
      | ~ ( v2_funct_1 @ X53 )
      | ( ( k2_relset_1 @ X54 @ X52 @ X53 )
       != X52 ) ) ),
    inference(demod,[status(thm)],['320','321'])).

thf('323',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['319','322'])).

thf('324',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('325',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('326',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['309','310','311'])).

thf('327',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('328',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('329',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['323','324','325','326','327','328'])).

thf('330',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['329'])).

thf('331',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('332',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['330','331'])).

thf('333',plain,
    ( ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['316','317'])).

thf('334',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('335',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['333','334'])).

thf('336',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['283','284'])).

thf('337',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['309','310','311'])).

thf('338',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('339',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['337','338'])).

thf('340',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['283','284'])).

thf('341',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('342',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['339','340','341'])).

thf('343',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['335','336','342'])).

thf('344',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_C )
      = ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['332','343'])).

thf('345',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('346',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('347',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['345','346'])).

thf('348',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('349',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['347','348'])).

thf('350',plain,(
    ! [X5: $i] :
      ( ( ( k5_relat_1 @ X5 @ ( k6_relat_1 @ ( k2_relat_1 @ X5 ) ) )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('351',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['349','350'])).

thf('352',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['283','284'])).

thf('353',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['351','352'])).

thf('354',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['283','284'])).

thf('355',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['344','353','354'])).

thf('356',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('357',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['355','356'])).

thf('358',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('359',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['283','284'])).

thf('360',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['357','358','359'])).

thf('361',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ sk_C ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['318','360'])).

thf('362',plain,
    ( ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['316','317'])).

thf('363',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['339','340','341'])).

thf('364',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['361','362','363'])).

thf('365',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('366',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['364','365'])).

thf('367',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('368',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('369',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['366','367','368'])).

thf('370',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k7_relat_1 @ X0 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['301','369'])).

thf('371',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k7_relat_1 @ X0 @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['370'])).

thf('372',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k7_relat_1 @ X7 @ X6 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X6 ) @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('373',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ sk_A ) @ sk_A )
        = ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['371','372'])).

thf('374',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) )
    | ( ( k7_relat_1 @ ( k7_relat_1 @ ( k4_relat_1 @ sk_D ) @ sk_A ) @ sk_A )
      = ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k4_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['300','373'])).

thf('375',plain,
    ( ( k7_relat_1 @ ( k4_relat_1 @ sk_D ) @ sk_A )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['298','299'])).

thf('376',plain,
    ( ( k7_relat_1 @ ( k4_relat_1 @ sk_D ) @ sk_A )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['298','299'])).

thf('377',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) )
    | ( ( k4_relat_1 @ sk_D )
      = ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k4_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['374','375','376'])).

thf('378',plain,
    ( ( ( k4_relat_1 @ sk_D )
      = ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k4_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['377'])).

thf('379',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k4_relat_1 @ sk_D )
      = ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k4_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['289','378'])).

thf('380',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['85','86'])).

thf('381',plain,
    ( ( k4_relat_1 @ sk_D )
    = ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k4_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['379','380'])).

thf('382',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['351','352'])).

thf('383',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('384',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k2_funct_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['213'])).

thf('385',plain,
    ( ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['383','384'])).

thf('386',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['85','86'])).

thf('387',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('388',plain,
    ( ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['385','386','387'])).

thf('389',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['128','129'])).

thf('390',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['388','389'])).

thf('391',plain,
    ( ( k2_funct_1 @ sk_D )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['248','249'])).

thf('392',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['390','391'])).

thf('393',plain,
    ( ( k4_relat_1 @ sk_D )
    = sk_C ),
    inference(demod,[status(thm)],['288','381','382','392'])).

thf('394',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('395',plain,
    ( ( k4_relat_1 @ sk_D )
    = sk_C ),
    inference(demod,[status(thm)],['288','381','382','392'])).

thf('396',plain,
    ( sk_D
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['252','393','394','395'])).

thf('397',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('398',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['309','310','311'])).

thf('399',plain,(
    sk_D
 != ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['397','398'])).

thf('400',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['396','399'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FuFZZPA2p0
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:51:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 3.34/3.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.34/3.52  % Solved by: fo/fo7.sh
% 3.34/3.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.34/3.52  % done 1910 iterations in 3.023s
% 3.34/3.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.34/3.52  % SZS output start Refutation
% 3.34/3.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.34/3.52  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 3.34/3.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.34/3.52  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 3.34/3.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.34/3.52  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.34/3.52  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 3.34/3.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.34/3.52  thf(sk_D_type, type, sk_D: $i).
% 3.34/3.52  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 3.34/3.52  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.34/3.52  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 3.34/3.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.34/3.52  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.34/3.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.34/3.52  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.34/3.52  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.34/3.52  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 3.34/3.52  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.34/3.52  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 3.34/3.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.34/3.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.34/3.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.34/3.52  thf(sk_B_type, type, sk_B: $i).
% 3.34/3.52  thf(sk_A_type, type, sk_A: $i).
% 3.34/3.52  thf(sk_C_type, type, sk_C: $i).
% 3.34/3.52  thf(t65_funct_1, axiom,
% 3.34/3.52    (![A:$i]:
% 3.34/3.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.34/3.52       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 3.34/3.52  thf('0', plain,
% 3.34/3.52      (![X13 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X13)
% 3.34/3.52          | ((k2_funct_1 @ (k2_funct_1 @ X13)) = (X13))
% 3.34/3.52          | ~ (v1_funct_1 @ X13)
% 3.34/3.52          | ~ (v1_relat_1 @ X13))),
% 3.34/3.52      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.34/3.52  thf(dt_k2_funct_1, axiom,
% 3.34/3.52    (![A:$i]:
% 3.34/3.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.34/3.52       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 3.34/3.52         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 3.34/3.52  thf('1', plain,
% 3.34/3.52      (![X10 : $i]:
% 3.34/3.52         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 3.34/3.52          | ~ (v1_funct_1 @ X10)
% 3.34/3.52          | ~ (v1_relat_1 @ X10))),
% 3.34/3.52      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.34/3.52  thf('2', plain,
% 3.34/3.52      (![X10 : $i]:
% 3.34/3.52         ((v1_funct_1 @ (k2_funct_1 @ X10))
% 3.34/3.52          | ~ (v1_funct_1 @ X10)
% 3.34/3.52          | ~ (v1_relat_1 @ X10))),
% 3.34/3.52      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.34/3.52  thf('3', plain,
% 3.34/3.52      (![X13 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X13)
% 3.34/3.52          | ((k2_funct_1 @ (k2_funct_1 @ X13)) = (X13))
% 3.34/3.52          | ~ (v1_funct_1 @ X13)
% 3.34/3.52          | ~ (v1_relat_1 @ X13))),
% 3.34/3.52      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.34/3.52  thf('4', plain,
% 3.34/3.52      (![X10 : $i]:
% 3.34/3.52         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 3.34/3.52          | ~ (v1_funct_1 @ X10)
% 3.34/3.52          | ~ (v1_relat_1 @ X10))),
% 3.34/3.52      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.34/3.52  thf('5', plain,
% 3.34/3.52      (![X10 : $i]:
% 3.34/3.52         ((v1_funct_1 @ (k2_funct_1 @ X10))
% 3.34/3.52          | ~ (v1_funct_1 @ X10)
% 3.34/3.52          | ~ (v1_relat_1 @ X10))),
% 3.34/3.52      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.34/3.52  thf('6', plain,
% 3.34/3.52      (![X13 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X13)
% 3.34/3.52          | ((k2_funct_1 @ (k2_funct_1 @ X13)) = (X13))
% 3.34/3.52          | ~ (v1_funct_1 @ X13)
% 3.34/3.52          | ~ (v1_relat_1 @ X13))),
% 3.34/3.52      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.34/3.52  thf('7', plain,
% 3.34/3.52      (![X10 : $i]:
% 3.34/3.52         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 3.34/3.52          | ~ (v1_funct_1 @ X10)
% 3.34/3.52          | ~ (v1_relat_1 @ X10))),
% 3.34/3.52      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.34/3.52  thf('8', plain,
% 3.34/3.52      (![X10 : $i]:
% 3.34/3.52         ((v1_funct_1 @ (k2_funct_1 @ X10))
% 3.34/3.52          | ~ (v1_funct_1 @ X10)
% 3.34/3.52          | ~ (v1_relat_1 @ X10))),
% 3.34/3.52      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.34/3.52  thf(d9_funct_1, axiom,
% 3.34/3.52    (![A:$i]:
% 3.34/3.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.34/3.52       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 3.34/3.52  thf('9', plain,
% 3.34/3.52      (![X9 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X9)
% 3.34/3.52          | ((k2_funct_1 @ X9) = (k4_relat_1 @ X9))
% 3.34/3.52          | ~ (v1_funct_1 @ X9)
% 3.34/3.52          | ~ (v1_relat_1 @ X9))),
% 3.34/3.52      inference('cnf', [status(esa)], [d9_funct_1])).
% 3.34/3.52  thf('10', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.34/3.52          | ((k2_funct_1 @ (k2_funct_1 @ X0))
% 3.34/3.52              = (k4_relat_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 3.34/3.52      inference('sup-', [status(thm)], ['8', '9'])).
% 3.34/3.52  thf('11', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.34/3.52          | ((k2_funct_1 @ (k2_funct_1 @ X0))
% 3.34/3.52              = (k4_relat_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0))),
% 3.34/3.52      inference('sup-', [status(thm)], ['7', '10'])).
% 3.34/3.52  thf('12', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (((k2_funct_1 @ (k2_funct_1 @ X0)) = (k4_relat_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0))),
% 3.34/3.52      inference('simplify', [status(thm)], ['11'])).
% 3.34/3.52  thf('13', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.34/3.52          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.34/3.52          | ((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52              = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 3.34/3.52      inference('sup-', [status(thm)], ['6', '12'])).
% 3.34/3.52  thf('14', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52            = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 3.34/3.52          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.34/3.52          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0))),
% 3.34/3.52      inference('simplify', [status(thm)], ['13'])).
% 3.34/3.52  thf('15', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.34/3.52          | ((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52              = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 3.34/3.52      inference('sup-', [status(thm)], ['5', '14'])).
% 3.34/3.52  thf('16', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52            = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 3.34/3.52          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0))),
% 3.34/3.52      inference('simplify', [status(thm)], ['15'])).
% 3.34/3.52  thf('17', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52              = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 3.34/3.52      inference('sup-', [status(thm)], ['4', '16'])).
% 3.34/3.52  thf('18', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52            = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0))),
% 3.34/3.52      inference('simplify', [status(thm)], ['17'])).
% 3.34/3.52  thf('19', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (((k2_funct_1 @ X0) = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0))),
% 3.34/3.52      inference('sup+', [status(thm)], ['3', '18'])).
% 3.34/3.52  thf('20', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ((k2_funct_1 @ X0)
% 3.34/3.52              = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 3.34/3.52      inference('simplify', [status(thm)], ['19'])).
% 3.34/3.52  thf('21', plain,
% 3.34/3.52      (![X10 : $i]:
% 3.34/3.52         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 3.34/3.52          | ~ (v1_funct_1 @ X10)
% 3.34/3.52          | ~ (v1_relat_1 @ X10))),
% 3.34/3.52      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.34/3.52  thf(t37_relat_1, axiom,
% 3.34/3.52    (![A:$i]:
% 3.34/3.52     ( ( v1_relat_1 @ A ) =>
% 3.34/3.52       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 3.34/3.52         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 3.34/3.52  thf('22', plain,
% 3.34/3.52      (![X1 : $i]:
% 3.34/3.52         (((k1_relat_1 @ X1) = (k2_relat_1 @ (k4_relat_1 @ X1)))
% 3.34/3.52          | ~ (v1_relat_1 @ X1))),
% 3.34/3.52      inference('cnf', [status(esa)], [t37_relat_1])).
% 3.34/3.52  thf('23', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ((k1_relat_1 @ (k2_funct_1 @ X0))
% 3.34/3.52              = (k2_relat_1 @ (k4_relat_1 @ (k2_funct_1 @ X0)))))),
% 3.34/3.52      inference('sup-', [status(thm)], ['21', '22'])).
% 3.34/3.52  thf('24', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.34/3.52          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 3.34/3.52      inference('sup+', [status(thm)], ['20', '23'])).
% 3.34/3.52  thf('25', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 3.34/3.52      inference('sup-', [status(thm)], ['2', '24'])).
% 3.34/3.52  thf('26', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0))),
% 3.34/3.52      inference('simplify', [status(thm)], ['25'])).
% 3.34/3.52  thf('27', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 3.34/3.52      inference('sup-', [status(thm)], ['1', '26'])).
% 3.34/3.52  thf('28', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0))),
% 3.34/3.52      inference('simplify', [status(thm)], ['27'])).
% 3.34/3.52  thf('29', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (((k1_relat_1 @ X0) = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0))),
% 3.34/3.52      inference('sup+', [status(thm)], ['0', '28'])).
% 3.34/3.52  thf('30', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ((k1_relat_1 @ X0) = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 3.34/3.52      inference('simplify', [status(thm)], ['29'])).
% 3.34/3.52  thf('31', plain,
% 3.34/3.52      (![X13 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X13)
% 3.34/3.52          | ((k2_funct_1 @ (k2_funct_1 @ X13)) = (X13))
% 3.34/3.52          | ~ (v1_funct_1 @ X13)
% 3.34/3.52          | ~ (v1_relat_1 @ X13))),
% 3.34/3.52      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.34/3.52  thf('32', plain,
% 3.34/3.52      (![X13 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X13)
% 3.34/3.52          | ((k2_funct_1 @ (k2_funct_1 @ X13)) = (X13))
% 3.34/3.52          | ~ (v1_funct_1 @ X13)
% 3.34/3.52          | ~ (v1_relat_1 @ X13))),
% 3.34/3.52      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.34/3.52  thf('33', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0))),
% 3.34/3.52      inference('simplify', [status(thm)], ['27'])).
% 3.34/3.52  thf(t98_relat_1, axiom,
% 3.34/3.52    (![A:$i]:
% 3.34/3.52     ( ( v1_relat_1 @ A ) =>
% 3.34/3.52       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 3.34/3.52  thf('34', plain,
% 3.34/3.52      (![X8 : $i]:
% 3.34/3.52         (((k7_relat_1 @ X8 @ (k1_relat_1 @ X8)) = (X8)) | ~ (v1_relat_1 @ X8))),
% 3.34/3.52      inference('cnf', [status(esa)], [t98_relat_1])).
% 3.34/3.52  thf('35', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (((k7_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 3.34/3.52            (k2_relat_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52            = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 3.34/3.52      inference('sup+', [status(thm)], ['33', '34'])).
% 3.34/3.52  thf('36', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ((k7_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 3.34/3.52              (k2_relat_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 3.34/3.52      inference('sup-', [status(thm)], ['32', '35'])).
% 3.34/3.52  thf('37', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (((k7_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 3.34/3.52            (k2_relat_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52            = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0))),
% 3.34/3.52      inference('simplify', [status(thm)], ['36'])).
% 3.34/3.52  thf('38', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (((k7_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52            = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0))),
% 3.34/3.52      inference('sup+', [status(thm)], ['31', '37'])).
% 3.34/3.52  thf('39', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ((k7_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 3.34/3.52      inference('simplify', [status(thm)], ['38'])).
% 3.34/3.52  thf('40', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (((k7_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 3.34/3.52            = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0))),
% 3.34/3.52      inference('sup+', [status(thm)], ['30', '39'])).
% 3.34/3.52  thf('41', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 3.34/3.52              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 3.34/3.52      inference('simplify', [status(thm)], ['40'])).
% 3.34/3.52  thf(t94_relat_1, axiom,
% 3.34/3.52    (![A:$i,B:$i]:
% 3.34/3.52     ( ( v1_relat_1 @ B ) =>
% 3.34/3.52       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 3.34/3.52  thf('42', plain,
% 3.34/3.52      (![X6 : $i, X7 : $i]:
% 3.34/3.52         (((k7_relat_1 @ X7 @ X6) = (k5_relat_1 @ (k6_relat_1 @ X6) @ X7))
% 3.34/3.52          | ~ (v1_relat_1 @ X7))),
% 3.34/3.52      inference('cnf', [status(esa)], [t94_relat_1])).
% 3.34/3.52  thf('43', plain,
% 3.34/3.52      (![X8 : $i]:
% 3.34/3.52         (((k7_relat_1 @ X8 @ (k1_relat_1 @ X8)) = (X8)) | ~ (v1_relat_1 @ X8))),
% 3.34/3.52      inference('cnf', [status(esa)], [t98_relat_1])).
% 3.34/3.52  thf(t36_funct_2, conjecture,
% 3.34/3.52    (![A:$i,B:$i,C:$i]:
% 3.34/3.52     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.34/3.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.34/3.52       ( ![D:$i]:
% 3.34/3.52         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.34/3.52             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.34/3.52           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 3.34/3.52               ( r2_relset_1 @
% 3.34/3.52                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.34/3.52                 ( k6_partfun1 @ A ) ) & 
% 3.34/3.52               ( v2_funct_1 @ C ) ) =>
% 3.34/3.52             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.34/3.52               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 3.34/3.52  thf(zf_stmt_0, negated_conjecture,
% 3.34/3.52    (~( ![A:$i,B:$i,C:$i]:
% 3.34/3.52        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.34/3.52            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.34/3.52          ( ![D:$i]:
% 3.34/3.52            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.34/3.52                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.34/3.52              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 3.34/3.52                  ( r2_relset_1 @
% 3.34/3.52                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.34/3.52                    ( k6_partfun1 @ A ) ) & 
% 3.34/3.52                  ( v2_funct_1 @ C ) ) =>
% 3.34/3.52                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.34/3.52                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 3.34/3.52    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 3.34/3.52  thf('44', plain,
% 3.34/3.52      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.34/3.52        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.34/3.52        (k6_partfun1 @ sk_A))),
% 3.34/3.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.52  thf(redefinition_k6_partfun1, axiom,
% 3.34/3.52    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 3.34/3.52  thf('45', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 3.34/3.52      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.34/3.52  thf('46', plain,
% 3.34/3.52      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.34/3.52        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.34/3.52        (k6_relat_1 @ sk_A))),
% 3.34/3.52      inference('demod', [status(thm)], ['44', '45'])).
% 3.34/3.52  thf('47', plain,
% 3.34/3.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.34/3.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.52  thf('48', plain,
% 3.34/3.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.34/3.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.52  thf(dt_k1_partfun1, axiom,
% 3.34/3.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.34/3.52     ( ( ( v1_funct_1 @ E ) & 
% 3.34/3.52         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.34/3.52         ( v1_funct_1 @ F ) & 
% 3.34/3.52         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.34/3.52       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 3.34/3.52         ( m1_subset_1 @
% 3.34/3.52           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 3.34/3.52           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 3.34/3.52  thf('49', plain,
% 3.34/3.52      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 3.34/3.52         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 3.34/3.52          | ~ (v1_funct_1 @ X24)
% 3.34/3.52          | ~ (v1_funct_1 @ X27)
% 3.34/3.52          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 3.34/3.52          | (m1_subset_1 @ (k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27) @ 
% 3.34/3.52             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X29))))),
% 3.34/3.52      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 3.34/3.52  thf('50', plain,
% 3.34/3.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.34/3.52         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.34/3.52           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.34/3.52          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.34/3.52          | ~ (v1_funct_1 @ X1)
% 3.34/3.52          | ~ (v1_funct_1 @ sk_C))),
% 3.34/3.52      inference('sup-', [status(thm)], ['48', '49'])).
% 3.34/3.52  thf('51', plain, ((v1_funct_1 @ sk_C)),
% 3.34/3.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.52  thf('52', plain,
% 3.34/3.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.34/3.52         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.34/3.52           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.34/3.52          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.34/3.52          | ~ (v1_funct_1 @ X1))),
% 3.34/3.52      inference('demod', [status(thm)], ['50', '51'])).
% 3.34/3.52  thf('53', plain,
% 3.34/3.52      ((~ (v1_funct_1 @ sk_D)
% 3.34/3.52        | (m1_subset_1 @ 
% 3.34/3.52           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.34/3.52           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.34/3.52      inference('sup-', [status(thm)], ['47', '52'])).
% 3.34/3.52  thf('54', plain, ((v1_funct_1 @ sk_D)),
% 3.34/3.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.52  thf('55', plain,
% 3.34/3.52      ((m1_subset_1 @ 
% 3.34/3.52        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.34/3.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.34/3.52      inference('demod', [status(thm)], ['53', '54'])).
% 3.34/3.52  thf(redefinition_r2_relset_1, axiom,
% 3.34/3.52    (![A:$i,B:$i,C:$i,D:$i]:
% 3.34/3.52     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.34/3.52         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.34/3.52       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.34/3.52  thf('56', plain,
% 3.34/3.52      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 3.34/3.52         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 3.34/3.52          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 3.34/3.52          | ((X20) = (X23))
% 3.34/3.52          | ~ (r2_relset_1 @ X21 @ X22 @ X20 @ X23))),
% 3.34/3.52      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.34/3.52  thf('57', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.34/3.52             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 3.34/3.52          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 3.34/3.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.34/3.52      inference('sup-', [status(thm)], ['55', '56'])).
% 3.34/3.52  thf('58', plain,
% 3.34/3.52      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 3.34/3.52           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.34/3.52        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.34/3.52            = (k6_relat_1 @ sk_A)))),
% 3.34/3.52      inference('sup-', [status(thm)], ['46', '57'])).
% 3.34/3.52  thf(dt_k6_partfun1, axiom,
% 3.34/3.52    (![A:$i]:
% 3.34/3.52     ( ( m1_subset_1 @
% 3.34/3.52         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 3.34/3.52       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 3.34/3.52  thf('59', plain,
% 3.34/3.52      (![X31 : $i]:
% 3.34/3.52         (m1_subset_1 @ (k6_partfun1 @ X31) @ 
% 3.34/3.52          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 3.34/3.52      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 3.34/3.52  thf('60', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 3.34/3.52      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.34/3.52  thf('61', plain,
% 3.34/3.52      (![X31 : $i]:
% 3.34/3.52         (m1_subset_1 @ (k6_relat_1 @ X31) @ 
% 3.34/3.52          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 3.34/3.52      inference('demod', [status(thm)], ['59', '60'])).
% 3.34/3.52  thf('62', plain,
% 3.34/3.52      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.34/3.52         = (k6_relat_1 @ sk_A))),
% 3.34/3.52      inference('demod', [status(thm)], ['58', '61'])).
% 3.34/3.52  thf('63', plain,
% 3.34/3.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.34/3.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.52  thf(t24_funct_2, axiom,
% 3.34/3.52    (![A:$i,B:$i,C:$i]:
% 3.34/3.52     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.34/3.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.34/3.52       ( ![D:$i]:
% 3.34/3.52         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.34/3.52             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.34/3.52           ( ( r2_relset_1 @
% 3.34/3.52               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 3.34/3.52               ( k6_partfun1 @ B ) ) =>
% 3.34/3.52             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 3.34/3.52  thf('64', plain,
% 3.34/3.52      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 3.34/3.52         (~ (v1_funct_1 @ X39)
% 3.34/3.52          | ~ (v1_funct_2 @ X39 @ X40 @ X41)
% 3.34/3.52          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 3.34/3.52          | ~ (r2_relset_1 @ X40 @ X40 @ 
% 3.34/3.52               (k1_partfun1 @ X40 @ X41 @ X41 @ X40 @ X39 @ X42) @ 
% 3.34/3.52               (k6_partfun1 @ X40))
% 3.34/3.52          | ((k2_relset_1 @ X41 @ X40 @ X42) = (X40))
% 3.34/3.52          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40)))
% 3.34/3.52          | ~ (v1_funct_2 @ X42 @ X41 @ X40)
% 3.34/3.52          | ~ (v1_funct_1 @ X42))),
% 3.34/3.52      inference('cnf', [status(esa)], [t24_funct_2])).
% 3.34/3.52  thf('65', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 3.34/3.52      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.34/3.52  thf('66', plain,
% 3.34/3.52      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 3.34/3.52         (~ (v1_funct_1 @ X39)
% 3.34/3.52          | ~ (v1_funct_2 @ X39 @ X40 @ X41)
% 3.34/3.52          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 3.34/3.52          | ~ (r2_relset_1 @ X40 @ X40 @ 
% 3.34/3.52               (k1_partfun1 @ X40 @ X41 @ X41 @ X40 @ X39 @ X42) @ 
% 3.34/3.52               (k6_relat_1 @ X40))
% 3.34/3.52          | ((k2_relset_1 @ X41 @ X40 @ X42) = (X40))
% 3.34/3.52          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40)))
% 3.34/3.52          | ~ (v1_funct_2 @ X42 @ X41 @ X40)
% 3.34/3.52          | ~ (v1_funct_1 @ X42))),
% 3.34/3.52      inference('demod', [status(thm)], ['64', '65'])).
% 3.34/3.52  thf('67', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 3.34/3.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.34/3.52          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 3.34/3.52          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.34/3.52               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 3.34/3.52               (k6_relat_1 @ sk_A))
% 3.34/3.52          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.34/3.52          | ~ (v1_funct_1 @ sk_C))),
% 3.34/3.52      inference('sup-', [status(thm)], ['63', '66'])).
% 3.34/3.52  thf('68', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.34/3.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.52  thf('69', plain, ((v1_funct_1 @ sk_C)),
% 3.34/3.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.52  thf('70', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 3.34/3.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.34/3.52          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 3.34/3.52          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.34/3.52               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 3.34/3.52               (k6_relat_1 @ sk_A)))),
% 3.34/3.52      inference('demod', [status(thm)], ['67', '68', '69'])).
% 3.34/3.52  thf('71', plain,
% 3.34/3.52      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 3.34/3.52           (k6_relat_1 @ sk_A))
% 3.34/3.52        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 3.34/3.52        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.34/3.52        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.34/3.52        | ~ (v1_funct_1 @ sk_D))),
% 3.34/3.52      inference('sup-', [status(thm)], ['62', '70'])).
% 3.34/3.52  thf('72', plain,
% 3.34/3.52      (![X31 : $i]:
% 3.34/3.52         (m1_subset_1 @ (k6_relat_1 @ X31) @ 
% 3.34/3.52          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 3.34/3.52      inference('demod', [status(thm)], ['59', '60'])).
% 3.34/3.52  thf('73', plain,
% 3.34/3.52      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 3.34/3.52         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 3.34/3.52          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 3.34/3.52          | (r2_relset_1 @ X21 @ X22 @ X20 @ X23)
% 3.34/3.52          | ((X20) != (X23)))),
% 3.34/3.52      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.34/3.52  thf('74', plain,
% 3.34/3.52      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.34/3.52         ((r2_relset_1 @ X21 @ X22 @ X23 @ X23)
% 3.34/3.52          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 3.34/3.52      inference('simplify', [status(thm)], ['73'])).
% 3.34/3.52  thf('75', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 3.34/3.52      inference('sup-', [status(thm)], ['72', '74'])).
% 3.34/3.52  thf('76', plain,
% 3.34/3.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.34/3.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.52  thf(redefinition_k2_relset_1, axiom,
% 3.34/3.52    (![A:$i,B:$i,C:$i]:
% 3.34/3.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.34/3.52       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.34/3.52  thf('77', plain,
% 3.34/3.52      (![X17 : $i, X18 : $i, X19 : $i]:
% 3.34/3.52         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 3.34/3.52          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 3.34/3.52      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.34/3.52  thf('78', plain,
% 3.34/3.52      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 3.34/3.52      inference('sup-', [status(thm)], ['76', '77'])).
% 3.34/3.52  thf('79', plain,
% 3.34/3.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.34/3.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.52  thf('80', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.34/3.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.52  thf('81', plain, ((v1_funct_1 @ sk_D)),
% 3.34/3.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.52  thf('82', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.34/3.52      inference('demod', [status(thm)], ['71', '75', '78', '79', '80', '81'])).
% 3.34/3.52  thf(t80_relat_1, axiom,
% 3.34/3.52    (![A:$i]:
% 3.34/3.52     ( ( v1_relat_1 @ A ) =>
% 3.34/3.52       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 3.34/3.52  thf('83', plain,
% 3.34/3.52      (![X5 : $i]:
% 3.34/3.52         (((k5_relat_1 @ X5 @ (k6_relat_1 @ (k2_relat_1 @ X5))) = (X5))
% 3.34/3.52          | ~ (v1_relat_1 @ X5))),
% 3.34/3.52      inference('cnf', [status(esa)], [t80_relat_1])).
% 3.34/3.52  thf('84', plain,
% 3.34/3.52      ((((k5_relat_1 @ sk_D @ (k6_relat_1 @ sk_A)) = (sk_D))
% 3.34/3.52        | ~ (v1_relat_1 @ sk_D))),
% 3.34/3.52      inference('sup+', [status(thm)], ['82', '83'])).
% 3.34/3.52  thf('85', plain,
% 3.34/3.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.34/3.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.52  thf(cc1_relset_1, axiom,
% 3.34/3.52    (![A:$i,B:$i,C:$i]:
% 3.34/3.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.34/3.52       ( v1_relat_1 @ C ) ))).
% 3.34/3.52  thf('86', plain,
% 3.34/3.52      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.34/3.52         ((v1_relat_1 @ X14)
% 3.34/3.52          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 3.34/3.52      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.34/3.52  thf('87', plain, ((v1_relat_1 @ sk_D)),
% 3.34/3.52      inference('sup-', [status(thm)], ['85', '86'])).
% 3.34/3.52  thf('88', plain, (((k5_relat_1 @ sk_D @ (k6_relat_1 @ sk_A)) = (sk_D))),
% 3.34/3.52      inference('demod', [status(thm)], ['84', '87'])).
% 3.34/3.52  thf('89', plain,
% 3.34/3.52      (![X6 : $i, X7 : $i]:
% 3.34/3.52         (((k7_relat_1 @ X7 @ X6) = (k5_relat_1 @ (k6_relat_1 @ X6) @ X7))
% 3.34/3.52          | ~ (v1_relat_1 @ X7))),
% 3.34/3.52      inference('cnf', [status(esa)], [t94_relat_1])).
% 3.34/3.52  thf(t55_relat_1, axiom,
% 3.34/3.52    (![A:$i]:
% 3.34/3.52     ( ( v1_relat_1 @ A ) =>
% 3.34/3.52       ( ![B:$i]:
% 3.34/3.52         ( ( v1_relat_1 @ B ) =>
% 3.34/3.52           ( ![C:$i]:
% 3.34/3.52             ( ( v1_relat_1 @ C ) =>
% 3.34/3.52               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 3.34/3.52                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 3.34/3.52  thf('90', plain,
% 3.34/3.52      (![X2 : $i, X3 : $i, X4 : $i]:
% 3.34/3.52         (~ (v1_relat_1 @ X2)
% 3.34/3.52          | ((k5_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 3.34/3.52              = (k5_relat_1 @ X3 @ (k5_relat_1 @ X2 @ X4)))
% 3.34/3.52          | ~ (v1_relat_1 @ X4)
% 3.34/3.52          | ~ (v1_relat_1 @ X3))),
% 3.34/3.52      inference('cnf', [status(esa)], [t55_relat_1])).
% 3.34/3.52  thf('91', plain,
% 3.34/3.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.34/3.52         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 3.34/3.52            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 3.34/3.52          | ~ (v1_relat_1 @ X1)
% 3.34/3.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 3.34/3.52          | ~ (v1_relat_1 @ X2)
% 3.34/3.52          | ~ (v1_relat_1 @ X1))),
% 3.34/3.52      inference('sup+', [status(thm)], ['89', '90'])).
% 3.34/3.52  thf(fc4_funct_1, axiom,
% 3.34/3.52    (![A:$i]:
% 3.34/3.52     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 3.34/3.52       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 3.34/3.52  thf('92', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 3.34/3.52      inference('cnf', [status(esa)], [fc4_funct_1])).
% 3.34/3.52  thf('93', plain,
% 3.34/3.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.34/3.52         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 3.34/3.52            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 3.34/3.52          | ~ (v1_relat_1 @ X1)
% 3.34/3.52          | ~ (v1_relat_1 @ X2)
% 3.34/3.52          | ~ (v1_relat_1 @ X1))),
% 3.34/3.52      inference('demod', [status(thm)], ['91', '92'])).
% 3.34/3.52  thf('94', plain,
% 3.34/3.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.34/3.52         (~ (v1_relat_1 @ X2)
% 3.34/3.52          | ~ (v1_relat_1 @ X1)
% 3.34/3.52          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 3.34/3.52              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 3.34/3.52      inference('simplify', [status(thm)], ['93'])).
% 3.34/3.52  thf('95', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (((k5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ (k6_relat_1 @ sk_A))
% 3.34/3.52            = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_D))
% 3.34/3.52          | ~ (v1_relat_1 @ sk_D)
% 3.34/3.52          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 3.34/3.52      inference('sup+', [status(thm)], ['88', '94'])).
% 3.34/3.52  thf('96', plain, ((v1_relat_1 @ sk_D)),
% 3.34/3.52      inference('sup-', [status(thm)], ['85', '86'])).
% 3.34/3.52  thf('97', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 3.34/3.52      inference('cnf', [status(esa)], [fc4_funct_1])).
% 3.34/3.52  thf('98', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         ((k5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ (k6_relat_1 @ sk_A))
% 3.34/3.52           = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_D))),
% 3.34/3.52      inference('demod', [status(thm)], ['95', '96', '97'])).
% 3.34/3.52  thf('99', plain,
% 3.34/3.52      ((((k5_relat_1 @ sk_D @ (k6_relat_1 @ sk_A))
% 3.34/3.52          = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_D)) @ sk_D))
% 3.34/3.52        | ~ (v1_relat_1 @ sk_D))),
% 3.34/3.52      inference('sup+', [status(thm)], ['43', '98'])).
% 3.34/3.52  thf('100', plain, (((k5_relat_1 @ sk_D @ (k6_relat_1 @ sk_A)) = (sk_D))),
% 3.34/3.52      inference('demod', [status(thm)], ['84', '87'])).
% 3.34/3.52  thf('101', plain, ((v1_relat_1 @ sk_D)),
% 3.34/3.52      inference('sup-', [status(thm)], ['85', '86'])).
% 3.34/3.52  thf('102', plain,
% 3.34/3.52      (((sk_D) = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_D)) @ sk_D))),
% 3.34/3.52      inference('demod', [status(thm)], ['99', '100', '101'])).
% 3.34/3.52  thf('103', plain,
% 3.34/3.52      ((((sk_D) = (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))
% 3.34/3.52        | ~ (v1_relat_1 @ sk_D))),
% 3.34/3.52      inference('sup+', [status(thm)], ['42', '102'])).
% 3.34/3.52  thf('104', plain, ((v1_relat_1 @ sk_D)),
% 3.34/3.52      inference('sup-', [status(thm)], ['85', '86'])).
% 3.34/3.52  thf('105', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))),
% 3.34/3.52      inference('demod', [status(thm)], ['103', '104'])).
% 3.34/3.52  thf('106', plain,
% 3.34/3.52      ((((sk_D) = (k2_funct_1 @ (k2_funct_1 @ sk_D)))
% 3.34/3.52        | ~ (v1_relat_1 @ sk_D)
% 3.34/3.52        | ~ (v1_funct_1 @ sk_D)
% 3.34/3.52        | ~ (v2_funct_1 @ sk_D))),
% 3.34/3.52      inference('sup+', [status(thm)], ['41', '105'])).
% 3.34/3.52  thf('107', plain, ((v1_relat_1 @ sk_D)),
% 3.34/3.52      inference('sup-', [status(thm)], ['85', '86'])).
% 3.34/3.52  thf('108', plain, ((v1_funct_1 @ sk_D)),
% 3.34/3.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.52  thf('109', plain,
% 3.34/3.52      ((((sk_D) = (k2_funct_1 @ (k2_funct_1 @ sk_D))) | ~ (v2_funct_1 @ sk_D))),
% 3.34/3.52      inference('demod', [status(thm)], ['106', '107', '108'])).
% 3.34/3.52  thf('110', plain,
% 3.34/3.52      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.34/3.52         = (k6_relat_1 @ sk_A))),
% 3.34/3.52      inference('demod', [status(thm)], ['58', '61'])).
% 3.34/3.52  thf('111', plain,
% 3.34/3.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.34/3.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.52  thf(t30_funct_2, axiom,
% 3.34/3.52    (![A:$i,B:$i,C:$i,D:$i]:
% 3.34/3.52     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.34/3.52         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 3.34/3.52       ( ![E:$i]:
% 3.34/3.52         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 3.34/3.52             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 3.34/3.52           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 3.34/3.52               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 3.34/3.52             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 3.34/3.52               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 3.34/3.52  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 3.34/3.52  thf(zf_stmt_2, axiom,
% 3.34/3.52    (![C:$i,B:$i]:
% 3.34/3.52     ( ( zip_tseitin_1 @ C @ B ) =>
% 3.34/3.52       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 3.34/3.52  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 3.34/3.52  thf(zf_stmt_4, axiom,
% 3.34/3.52    (![E:$i,D:$i]:
% 3.34/3.52     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 3.34/3.52  thf(zf_stmt_5, axiom,
% 3.34/3.52    (![A:$i,B:$i,C:$i,D:$i]:
% 3.34/3.52     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.34/3.52         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.34/3.52       ( ![E:$i]:
% 3.34/3.52         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 3.34/3.52             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.34/3.52           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 3.34/3.52               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 3.34/3.52             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 3.34/3.52  thf('112', plain,
% 3.34/3.52      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 3.34/3.52         (~ (v1_funct_1 @ X47)
% 3.34/3.52          | ~ (v1_funct_2 @ X47 @ X48 @ X49)
% 3.34/3.52          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 3.34/3.52          | (zip_tseitin_0 @ X47 @ X50)
% 3.34/3.52          | ~ (v2_funct_1 @ (k1_partfun1 @ X51 @ X48 @ X48 @ X49 @ X50 @ X47))
% 3.34/3.52          | (zip_tseitin_1 @ X49 @ X48)
% 3.34/3.52          | ((k2_relset_1 @ X51 @ X48 @ X50) != (X48))
% 3.34/3.52          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X48)))
% 3.34/3.52          | ~ (v1_funct_2 @ X50 @ X51 @ X48)
% 3.34/3.52          | ~ (v1_funct_1 @ X50))),
% 3.34/3.52      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.34/3.52  thf('113', plain,
% 3.34/3.52      (![X0 : $i, X1 : $i]:
% 3.34/3.52         (~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.34/3.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.34/3.52          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 3.34/3.52          | (zip_tseitin_1 @ sk_A @ sk_B)
% 3.34/3.52          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 3.34/3.52          | (zip_tseitin_0 @ sk_D @ X0)
% 3.34/3.52          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.34/3.52          | ~ (v1_funct_1 @ sk_D))),
% 3.34/3.52      inference('sup-', [status(thm)], ['111', '112'])).
% 3.34/3.52  thf('114', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.34/3.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.52  thf('115', plain, ((v1_funct_1 @ sk_D)),
% 3.34/3.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.52  thf('116', plain,
% 3.34/3.52      (![X0 : $i, X1 : $i]:
% 3.34/3.52         (~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.34/3.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.34/3.52          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 3.34/3.52          | (zip_tseitin_1 @ sk_A @ sk_B)
% 3.34/3.52          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 3.34/3.52          | (zip_tseitin_0 @ sk_D @ X0))),
% 3.34/3.52      inference('demod', [status(thm)], ['113', '114', '115'])).
% 3.34/3.52  thf('117', plain,
% 3.34/3.52      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 3.34/3.52        | (zip_tseitin_0 @ sk_D @ sk_C)
% 3.34/3.52        | (zip_tseitin_1 @ sk_A @ sk_B)
% 3.34/3.52        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 3.34/3.52        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 3.34/3.52        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.34/3.52        | ~ (v1_funct_1 @ sk_C))),
% 3.34/3.52      inference('sup-', [status(thm)], ['110', '116'])).
% 3.34/3.52  thf('118', plain, (![X12 : $i]: (v2_funct_1 @ (k6_relat_1 @ X12))),
% 3.34/3.52      inference('cnf', [status(esa)], [fc4_funct_1])).
% 3.34/3.52  thf('119', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 3.34/3.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.52  thf('120', plain,
% 3.34/3.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.34/3.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.52  thf('121', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.34/3.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.52  thf('122', plain, ((v1_funct_1 @ sk_C)),
% 3.34/3.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.52  thf('123', plain,
% 3.34/3.52      (((zip_tseitin_0 @ sk_D @ sk_C)
% 3.34/3.52        | (zip_tseitin_1 @ sk_A @ sk_B)
% 3.34/3.52        | ((sk_B) != (sk_B)))),
% 3.34/3.52      inference('demod', [status(thm)],
% 3.34/3.52                ['117', '118', '119', '120', '121', '122'])).
% 3.34/3.52  thf('124', plain,
% 3.34/3.52      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 3.34/3.52      inference('simplify', [status(thm)], ['123'])).
% 3.34/3.52  thf('125', plain,
% 3.34/3.52      (![X45 : $i, X46 : $i]:
% 3.34/3.52         (((X45) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X45 @ X46))),
% 3.34/3.52      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.34/3.52  thf('126', plain,
% 3.34/3.52      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 3.34/3.52      inference('sup-', [status(thm)], ['124', '125'])).
% 3.34/3.52  thf('127', plain, (((sk_A) != (k1_xboole_0))),
% 3.34/3.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.52  thf('128', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 3.34/3.52      inference('simplify_reflect-', [status(thm)], ['126', '127'])).
% 3.34/3.52  thf('129', plain,
% 3.34/3.52      (![X43 : $i, X44 : $i]:
% 3.34/3.52         ((v2_funct_1 @ X44) | ~ (zip_tseitin_0 @ X44 @ X43))),
% 3.34/3.52      inference('cnf', [status(esa)], [zf_stmt_4])).
% 3.34/3.52  thf('130', plain, ((v2_funct_1 @ sk_D)),
% 3.34/3.52      inference('sup-', [status(thm)], ['128', '129'])).
% 3.34/3.52  thf('131', plain, (((sk_D) = (k2_funct_1 @ (k2_funct_1 @ sk_D)))),
% 3.34/3.52      inference('demod', [status(thm)], ['109', '130'])).
% 3.34/3.52  thf('132', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 3.34/3.52              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 3.34/3.52      inference('simplify', [status(thm)], ['40'])).
% 3.34/3.52  thf('133', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 3.34/3.52              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 3.34/3.52      inference('simplify', [status(thm)], ['40'])).
% 3.34/3.52  thf('134', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52            = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0))),
% 3.34/3.52      inference('simplify', [status(thm)], ['17'])).
% 3.34/3.52  thf('135', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (((k2_funct_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 3.34/3.52            = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0))),
% 3.34/3.52      inference('sup+', [status(thm)], ['133', '134'])).
% 3.34/3.52  thf('136', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ((k2_funct_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 3.34/3.52              = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 3.34/3.52      inference('simplify', [status(thm)], ['135'])).
% 3.34/3.52  thf('137', plain,
% 3.34/3.52      (![X13 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X13)
% 3.34/3.52          | ((k2_funct_1 @ (k2_funct_1 @ X13)) = (X13))
% 3.34/3.52          | ~ (v1_funct_1 @ X13)
% 3.34/3.52          | ~ (v1_relat_1 @ X13))),
% 3.34/3.52      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.34/3.52  thf('138', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 3.34/3.52              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 3.34/3.52      inference('simplify', [status(thm)], ['40'])).
% 3.34/3.52  thf('139', plain,
% 3.34/3.52      (![X10 : $i]:
% 3.34/3.52         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 3.34/3.52          | ~ (v1_funct_1 @ X10)
% 3.34/3.52          | ~ (v1_relat_1 @ X10))),
% 3.34/3.52      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.34/3.52  thf('140', plain,
% 3.34/3.52      (![X10 : $i]:
% 3.34/3.52         ((v1_funct_1 @ (k2_funct_1 @ X10))
% 3.34/3.52          | ~ (v1_funct_1 @ X10)
% 3.34/3.52          | ~ (v1_relat_1 @ X10))),
% 3.34/3.52      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.34/3.52  thf('141', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 3.34/3.52              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 3.34/3.52      inference('simplify', [status(thm)], ['40'])).
% 3.34/3.52  thf('142', plain,
% 3.34/3.52      (![X10 : $i]:
% 3.34/3.52         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 3.34/3.52          | ~ (v1_funct_1 @ X10)
% 3.34/3.52          | ~ (v1_relat_1 @ X10))),
% 3.34/3.52      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.34/3.52  thf('143', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         ((v1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.34/3.52          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 3.34/3.52      inference('sup+', [status(thm)], ['141', '142'])).
% 3.34/3.52  thf('144', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | (v1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 3.34/3.52      inference('sup-', [status(thm)], ['140', '143'])).
% 3.34/3.52  thf('145', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         ((v1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0))),
% 3.34/3.52      inference('simplify', [status(thm)], ['144'])).
% 3.34/3.52  thf('146', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | (v1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 3.34/3.52      inference('sup-', [status(thm)], ['139', '145'])).
% 3.34/3.52  thf('147', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         ((v1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0))),
% 3.34/3.52      inference('simplify', [status(thm)], ['146'])).
% 3.34/3.52  thf('148', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         ((v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0))),
% 3.34/3.52      inference('sup+', [status(thm)], ['138', '147'])).
% 3.34/3.52  thf('149', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 3.34/3.52      inference('simplify', [status(thm)], ['148'])).
% 3.34/3.52  thf('150', plain,
% 3.34/3.52      (![X13 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X13)
% 3.34/3.52          | ((k2_funct_1 @ (k2_funct_1 @ X13)) = (X13))
% 3.34/3.52          | ~ (v1_funct_1 @ X13)
% 3.34/3.52          | ~ (v1_relat_1 @ X13))),
% 3.34/3.52      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.34/3.52  thf('151', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 3.34/3.52              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 3.34/3.52      inference('simplify', [status(thm)], ['40'])).
% 3.34/3.52  thf('152', plain,
% 3.34/3.52      (![X10 : $i]:
% 3.34/3.52         ((v1_funct_1 @ (k2_funct_1 @ X10))
% 3.34/3.52          | ~ (v1_funct_1 @ X10)
% 3.34/3.52          | ~ (v1_relat_1 @ X10))),
% 3.34/3.52      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.34/3.52  thf('153', plain,
% 3.34/3.52      (![X10 : $i]:
% 3.34/3.52         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 3.34/3.52          | ~ (v1_funct_1 @ X10)
% 3.34/3.52          | ~ (v1_relat_1 @ X10))),
% 3.34/3.52      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.34/3.52  thf('154', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 3.34/3.52              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 3.34/3.52      inference('simplify', [status(thm)], ['40'])).
% 3.34/3.52  thf('155', plain,
% 3.34/3.52      (![X10 : $i]:
% 3.34/3.52         ((v1_funct_1 @ (k2_funct_1 @ X10))
% 3.34/3.52          | ~ (v1_funct_1 @ X10)
% 3.34/3.52          | ~ (v1_relat_1 @ X10))),
% 3.34/3.52      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.34/3.52  thf('156', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         ((v1_funct_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.34/3.52          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 3.34/3.52      inference('sup+', [status(thm)], ['154', '155'])).
% 3.34/3.52  thf('157', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | (v1_funct_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 3.34/3.52      inference('sup-', [status(thm)], ['153', '156'])).
% 3.34/3.52  thf('158', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         ((v1_funct_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0))),
% 3.34/3.52      inference('simplify', [status(thm)], ['157'])).
% 3.34/3.52  thf('159', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | (v1_funct_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 3.34/3.52      inference('sup-', [status(thm)], ['152', '158'])).
% 3.34/3.52  thf('160', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         ((v1_funct_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0))),
% 3.34/3.52      inference('simplify', [status(thm)], ['159'])).
% 3.34/3.52  thf('161', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0))),
% 3.34/3.52      inference('sup+', [status(thm)], ['151', '160'])).
% 3.34/3.52  thf('162', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 3.34/3.52      inference('simplify', [status(thm)], ['161'])).
% 3.34/3.52  thf('163', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52            = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0))),
% 3.34/3.52      inference('simplify', [status(thm)], ['17'])).
% 3.34/3.52  thf('164', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 3.34/3.52      inference('simplify', [status(thm)], ['148'])).
% 3.34/3.52  thf('165', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         ((v1_relat_1 @ 
% 3.34/3.52           (k2_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52          | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 3.34/3.52      inference('sup+', [status(thm)], ['163', '164'])).
% 3.34/3.52  thf('166', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | (v1_relat_1 @ 
% 3.34/3.52             (k2_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))),
% 3.34/3.52      inference('sup-', [status(thm)], ['162', '165'])).
% 3.34/3.52  thf('167', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         ((v1_relat_1 @ 
% 3.34/3.52           (k2_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 3.34/3.52          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52          | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0))),
% 3.34/3.52      inference('simplify', [status(thm)], ['166'])).
% 3.34/3.52  thf('168', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52          | (v1_relat_1 @ 
% 3.34/3.52             (k2_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))),
% 3.34/3.52      inference('sup-', [status(thm)], ['150', '167'])).
% 3.34/3.52  thf('169', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         ((v1_relat_1 @ 
% 3.34/3.52           (k2_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 3.34/3.52          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0))),
% 3.34/3.52      inference('simplify', [status(thm)], ['168'])).
% 3.34/3.52  thf('170', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | (v1_relat_1 @ 
% 3.34/3.52             (k2_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))),
% 3.34/3.52      inference('sup-', [status(thm)], ['149', '169'])).
% 3.34/3.52  thf('171', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         ((v1_relat_1 @ 
% 3.34/3.52           (k2_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0))),
% 3.34/3.52      inference('simplify', [status(thm)], ['170'])).
% 3.34/3.52  thf('172', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         ((v1_relat_1 @ (k2_funct_1 @ (k4_relat_1 @ X0)))
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0))),
% 3.34/3.52      inference('sup+', [status(thm)], ['137', '171'])).
% 3.34/3.52  thf('173', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | (v1_relat_1 @ (k2_funct_1 @ (k4_relat_1 @ X0))))),
% 3.34/3.52      inference('simplify', [status(thm)], ['172'])).
% 3.34/3.52  thf('174', plain,
% 3.34/3.52      (![X13 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X13)
% 3.34/3.52          | ((k2_funct_1 @ (k2_funct_1 @ X13)) = (X13))
% 3.34/3.52          | ~ (v1_funct_1 @ X13)
% 3.34/3.52          | ~ (v1_relat_1 @ X13))),
% 3.34/3.52      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.34/3.52  thf('175', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 3.34/3.52      inference('simplify', [status(thm)], ['161'])).
% 3.34/3.52  thf('176', plain,
% 3.34/3.52      (![X13 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X13)
% 3.34/3.52          | ((k2_funct_1 @ (k2_funct_1 @ X13)) = (X13))
% 3.34/3.52          | ~ (v1_funct_1 @ X13)
% 3.34/3.52          | ~ (v1_relat_1 @ X13))),
% 3.34/3.52      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.34/3.52  thf('177', plain,
% 3.34/3.52      (![X13 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X13)
% 3.34/3.52          | ((k2_funct_1 @ (k2_funct_1 @ X13)) = (X13))
% 3.34/3.52          | ~ (v1_funct_1 @ X13)
% 3.34/3.52          | ~ (v1_relat_1 @ X13))),
% 3.34/3.52      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.34/3.52  thf('178', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52            = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0))),
% 3.34/3.52      inference('simplify', [status(thm)], ['17'])).
% 3.34/3.52  thf('179', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 3.34/3.52      inference('simplify', [status(thm)], ['161'])).
% 3.34/3.52  thf('180', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         ((v1_funct_1 @ 
% 3.34/3.52           (k2_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52          | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 3.34/3.52      inference('sup+', [status(thm)], ['178', '179'])).
% 3.34/3.52  thf('181', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | (v1_funct_1 @ 
% 3.34/3.52             (k2_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))),
% 3.34/3.52      inference('sup-', [status(thm)], ['177', '180'])).
% 3.34/3.52  thf('182', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         ((v1_funct_1 @ 
% 3.34/3.52           (k2_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 3.34/3.52          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52          | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0))),
% 3.34/3.52      inference('simplify', [status(thm)], ['181'])).
% 3.34/3.52  thf('183', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52          | (v1_funct_1 @ 
% 3.34/3.52             (k2_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))),
% 3.34/3.52      inference('sup-', [status(thm)], ['176', '182'])).
% 3.34/3.52  thf('184', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         ((v1_funct_1 @ 
% 3.34/3.52           (k2_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 3.34/3.52          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0))),
% 3.34/3.52      inference('simplify', [status(thm)], ['183'])).
% 3.34/3.52  thf('185', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | (v1_funct_1 @ 
% 3.34/3.52             (k2_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))),
% 3.34/3.52      inference('sup-', [status(thm)], ['175', '184'])).
% 3.34/3.52  thf('186', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         ((v1_funct_1 @ 
% 3.34/3.52           (k2_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0))),
% 3.34/3.52      inference('simplify', [status(thm)], ['185'])).
% 3.34/3.52  thf('187', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         ((v1_funct_1 @ (k2_funct_1 @ (k4_relat_1 @ X0)))
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0))),
% 3.34/3.52      inference('sup+', [status(thm)], ['174', '186'])).
% 3.34/3.52  thf('188', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | (v1_funct_1 @ (k2_funct_1 @ (k4_relat_1 @ X0))))),
% 3.34/3.52      inference('simplify', [status(thm)], ['187'])).
% 3.34/3.52  thf('189', plain,
% 3.34/3.52      (![X13 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X13)
% 3.34/3.52          | ((k2_funct_1 @ (k2_funct_1 @ X13)) = (X13))
% 3.34/3.52          | ~ (v1_funct_1 @ X13)
% 3.34/3.52          | ~ (v1_relat_1 @ X13))),
% 3.34/3.52      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.34/3.52  thf('190', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 3.34/3.52      inference('simplify', [status(thm)], ['161'])).
% 3.34/3.52  thf('191', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 3.34/3.52      inference('simplify', [status(thm)], ['148'])).
% 3.34/3.52  thf('192', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 3.34/3.52              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 3.34/3.52      inference('simplify', [status(thm)], ['40'])).
% 3.34/3.52  thf('193', plain,
% 3.34/3.52      (![X13 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X13)
% 3.34/3.52          | ((k2_funct_1 @ (k2_funct_1 @ X13)) = (X13))
% 3.34/3.52          | ~ (v1_funct_1 @ X13)
% 3.34/3.52          | ~ (v1_relat_1 @ X13))),
% 3.34/3.52      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.34/3.52  thf('194', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ((k2_funct_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 3.34/3.52              = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 3.34/3.52      inference('simplify', [status(thm)], ['135'])).
% 3.34/3.52  thf('195', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (((k2_funct_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 3.34/3.52            = (k4_relat_1 @ X0))
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0))),
% 3.34/3.52      inference('sup+', [status(thm)], ['193', '194'])).
% 3.34/3.52  thf('196', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ((k2_funct_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 3.34/3.52              = (k4_relat_1 @ X0)))),
% 3.34/3.52      inference('simplify', [status(thm)], ['195'])).
% 3.34/3.52  thf('197', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) = (k4_relat_1 @ X0))
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0))),
% 3.34/3.52      inference('sup+', [status(thm)], ['192', '196'])).
% 3.34/3.52  thf('198', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52              = (k4_relat_1 @ X0)))),
% 3.34/3.52      inference('simplify', [status(thm)], ['197'])).
% 3.34/3.52  thf('199', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52              = (k4_relat_1 @ X0)))),
% 3.34/3.52      inference('simplify', [status(thm)], ['197'])).
% 3.34/3.52  thf('200', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (((k2_funct_1 @ (k2_funct_1 @ (k4_relat_1 @ X0)))
% 3.34/3.52            = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52          | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 3.34/3.52      inference('sup+', [status(thm)], ['198', '199'])).
% 3.34/3.52  thf('201', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ((k2_funct_1 @ (k2_funct_1 @ (k4_relat_1 @ X0)))
% 3.34/3.52              = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 3.34/3.52      inference('sup-', [status(thm)], ['191', '200'])).
% 3.34/3.52  thf('202', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (((k2_funct_1 @ (k2_funct_1 @ (k4_relat_1 @ X0)))
% 3.34/3.52            = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 3.34/3.52          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52          | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0))),
% 3.34/3.52      inference('simplify', [status(thm)], ['201'])).
% 3.34/3.52  thf('203', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52          | ((k2_funct_1 @ (k2_funct_1 @ (k4_relat_1 @ X0)))
% 3.34/3.52              = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 3.34/3.52      inference('sup-', [status(thm)], ['190', '202'])).
% 3.34/3.52  thf('204', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (((k2_funct_1 @ (k2_funct_1 @ (k4_relat_1 @ X0)))
% 3.34/3.52            = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 3.34/3.52          | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0))),
% 3.34/3.52      inference('simplify', [status(thm)], ['203'])).
% 3.34/3.52  thf('205', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ((k2_funct_1 @ (k2_funct_1 @ (k4_relat_1 @ X0)))
% 3.34/3.52              = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 3.34/3.52      inference('sup-', [status(thm)], ['189', '204'])).
% 3.34/3.52  thf('206', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (((k2_funct_1 @ (k2_funct_1 @ (k4_relat_1 @ X0)))
% 3.34/3.52            = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0))),
% 3.34/3.52      inference('simplify', [status(thm)], ['205'])).
% 3.34/3.52  thf('207', plain,
% 3.34/3.52      (![X10 : $i]:
% 3.34/3.52         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 3.34/3.52          | ~ (v1_funct_1 @ X10)
% 3.34/3.52          | ~ (v1_relat_1 @ X10))),
% 3.34/3.52      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.34/3.52  thf('208', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         ((v1_relat_1 @ (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ (k2_funct_1 @ (k4_relat_1 @ X0)))
% 3.34/3.52          | ~ (v1_funct_1 @ (k2_funct_1 @ (k4_relat_1 @ X0))))),
% 3.34/3.52      inference('sup+', [status(thm)], ['206', '207'])).
% 3.34/3.52  thf('209', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ (k2_funct_1 @ (k4_relat_1 @ X0)))
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | (v1_relat_1 @ (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 3.34/3.52      inference('sup-', [status(thm)], ['188', '208'])).
% 3.34/3.52  thf('210', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         ((v1_relat_1 @ (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 3.34/3.52          | ~ (v1_relat_1 @ (k2_funct_1 @ (k4_relat_1 @ X0)))
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0))),
% 3.34/3.52      inference('simplify', [status(thm)], ['209'])).
% 3.34/3.52  thf('211', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | (v1_relat_1 @ (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 3.34/3.52      inference('sup-', [status(thm)], ['173', '210'])).
% 3.34/3.52  thf('212', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         ((v1_relat_1 @ (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0))),
% 3.34/3.52      inference('simplify', [status(thm)], ['211'])).
% 3.34/3.52  thf('213', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         ((v1_relat_1 @ (k2_funct_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))))
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0))),
% 3.34/3.52      inference('sup+', [status(thm)], ['136', '212'])).
% 3.34/3.52  thf('214', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | (v1_relat_1 @ (k2_funct_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)))))),
% 3.34/3.52      inference('simplify', [status(thm)], ['213'])).
% 3.34/3.52  thf('215', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         ((v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0))),
% 3.34/3.52      inference('sup+', [status(thm)], ['132', '214'])).
% 3.34/3.52  thf('216', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 3.34/3.52      inference('simplify', [status(thm)], ['215'])).
% 3.34/3.52  thf('217', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 3.34/3.52              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 3.34/3.52      inference('simplify', [status(thm)], ['40'])).
% 3.34/3.52  thf('218', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ((k2_funct_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 3.34/3.52              = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 3.34/3.52      inference('simplify', [status(thm)], ['135'])).
% 3.34/3.52  thf('219', plain,
% 3.34/3.52      (![X13 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X13)
% 3.34/3.52          | ((k2_funct_1 @ (k2_funct_1 @ X13)) = (X13))
% 3.34/3.52          | ~ (v1_funct_1 @ X13)
% 3.34/3.52          | ~ (v1_relat_1 @ X13))),
% 3.34/3.52      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.34/3.52  thf('220', plain,
% 3.34/3.52      (![X13 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X13)
% 3.34/3.52          | ((k2_funct_1 @ (k2_funct_1 @ X13)) = (X13))
% 3.34/3.52          | ~ (v1_funct_1 @ X13)
% 3.34/3.52          | ~ (v1_relat_1 @ X13))),
% 3.34/3.52      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.34/3.52  thf('221', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52            = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0))),
% 3.34/3.52      inference('simplify', [status(thm)], ['17'])).
% 3.34/3.52  thf('222', plain,
% 3.34/3.52      (![X10 : $i]:
% 3.34/3.52         ((v1_funct_1 @ (k2_funct_1 @ X10))
% 3.34/3.52          | ~ (v1_funct_1 @ X10)
% 3.34/3.52          | ~ (v1_relat_1 @ X10))),
% 3.34/3.52      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.34/3.52  thf('223', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         ((v1_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 3.34/3.52      inference('sup+', [status(thm)], ['221', '222'])).
% 3.34/3.52  thf('224', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | (v1_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 3.34/3.52      inference('sup-', [status(thm)], ['220', '223'])).
% 3.34/3.52  thf('225', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         ((v1_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 3.34/3.52          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0))),
% 3.34/3.52      inference('simplify', [status(thm)], ['224'])).
% 3.34/3.52  thf('226', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | (v1_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 3.34/3.52      inference('sup-', [status(thm)], ['219', '225'])).
% 3.34/3.52  thf('227', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         ((v1_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0))),
% 3.34/3.52      inference('simplify', [status(thm)], ['226'])).
% 3.34/3.52  thf('228', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         ((v1_funct_1 @ (k2_funct_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))))
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0))),
% 3.34/3.52      inference('sup+', [status(thm)], ['218', '227'])).
% 3.34/3.52  thf('229', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | (v1_funct_1 @ (k2_funct_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)))))),
% 3.34/3.52      inference('simplify', [status(thm)], ['228'])).
% 3.34/3.52  thf('230', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0))),
% 3.34/3.52      inference('sup+', [status(thm)], ['217', '229'])).
% 3.34/3.52  thf('231', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0)
% 3.34/3.52          | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 3.34/3.52      inference('simplify', [status(thm)], ['230'])).
% 3.34/3.52  thf('232', plain,
% 3.34/3.52      (![X9 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X9)
% 3.34/3.52          | ((k2_funct_1 @ X9) = (k4_relat_1 @ X9))
% 3.34/3.52          | ~ (v1_funct_1 @ X9)
% 3.34/3.52          | ~ (v1_relat_1 @ X9))),
% 3.34/3.52      inference('cnf', [status(esa)], [d9_funct_1])).
% 3.34/3.52  thf('233', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 3.34/3.52          | ((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 3.34/3.52              = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 3.34/3.52          | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 3.34/3.52      inference('sup-', [status(thm)], ['231', '232'])).
% 3.34/3.52  thf('234', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (~ (v1_relat_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 3.34/3.52          | ((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 3.34/3.52              = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0))),
% 3.34/3.52      inference('sup-', [status(thm)], ['216', '233'])).
% 3.34/3.52  thf('235', plain,
% 3.34/3.52      (![X0 : $i]:
% 3.34/3.52         (((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 3.34/3.52            = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 3.34/3.52          | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 3.34/3.52          | ~ (v2_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_funct_1 @ X0)
% 3.34/3.52          | ~ (v1_relat_1 @ X0))),
% 3.34/3.52      inference('simplify', [status(thm)], ['234'])).
% 3.34/3.52  thf('236', plain,
% 3.34/3.52      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_D))
% 3.34/3.52        | ~ (v1_relat_1 @ sk_D)
% 3.34/3.52        | ~ (v1_funct_1 @ sk_D)
% 3.34/3.52        | ~ (v2_funct_1 @ sk_D)
% 3.34/3.52        | ((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_D))))
% 3.34/3.52            = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_D))))))),
% 3.34/3.52      inference('sup-', [status(thm)], ['131', '235'])).
% 3.34/3.52  thf('237', plain, ((v1_relat_1 @ sk_D)),
% 3.34/3.52      inference('sup-', [status(thm)], ['85', '86'])).
% 3.34/3.52  thf('238', plain, ((v1_funct_1 @ sk_D)),
% 3.34/3.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.52  thf('239', plain, ((v2_funct_1 @ sk_D)),
% 3.34/3.52      inference('sup-', [status(thm)], ['128', '129'])).
% 3.34/3.52  thf('240', plain, (((sk_D) = (k2_funct_1 @ (k2_funct_1 @ sk_D)))),
% 3.34/3.52      inference('demod', [status(thm)], ['109', '130'])).
% 3.34/3.52  thf('241', plain, (((sk_D) = (k2_funct_1 @ (k2_funct_1 @ sk_D)))),
% 3.34/3.52      inference('demod', [status(thm)], ['109', '130'])).
% 3.34/3.52  thf('242', plain, (((sk_D) = (k2_funct_1 @ (k2_funct_1 @ sk_D)))),
% 3.34/3.52      inference('demod', [status(thm)], ['109', '130'])).
% 3.34/3.52  thf('243', plain,
% 3.34/3.52      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_D))
% 3.34/3.52        | ((sk_D) = (k4_relat_1 @ (k2_funct_1 @ sk_D))))),
% 3.34/3.52      inference('demod', [status(thm)],
% 3.34/3.52                ['236', '237', '238', '239', '240', '241', '242'])).
% 3.34/3.52  thf('244', plain, ((v1_funct_1 @ sk_D)),
% 3.34/3.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.52  thf('245', plain,
% 3.34/3.52      (![X9 : $i]:
% 3.34/3.52         (~ (v2_funct_1 @ X9)
% 3.34/3.52          | ((k2_funct_1 @ X9) = (k4_relat_1 @ X9))
% 3.34/3.52          | ~ (v1_funct_1 @ X9)
% 3.34/3.52          | ~ (v1_relat_1 @ X9))),
% 3.34/3.52      inference('cnf', [status(esa)], [d9_funct_1])).
% 3.34/3.52  thf('246', plain,
% 3.34/3.52      ((~ (v1_relat_1 @ sk_D)
% 3.34/3.52        | ((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))
% 3.34/3.52        | ~ (v2_funct_1 @ sk_D))),
% 3.34/3.52      inference('sup-', [status(thm)], ['244', '245'])).
% 3.34/3.52  thf('247', plain, ((v1_relat_1 @ sk_D)),
% 3.34/3.52      inference('sup-', [status(thm)], ['85', '86'])).
% 3.34/3.52  thf('248', plain,
% 3.34/3.52      ((((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 3.34/3.52      inference('demod', [status(thm)], ['246', '247'])).
% 3.34/3.52  thf('249', plain, ((v2_funct_1 @ sk_D)),
% 3.34/3.52      inference('sup-', [status(thm)], ['128', '129'])).
% 3.34/3.52  thf('250', plain, (((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))),
% 3.34/3.52      inference('demod', [status(thm)], ['248', '249'])).
% 3.34/3.52  thf('251', plain, (((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))),
% 3.34/3.52      inference('demod', [status(thm)], ['248', '249'])).
% 3.34/3.52  thf('252', plain,
% 3.34/3.52      ((~ (v2_funct_1 @ (k4_relat_1 @ sk_D))
% 3.34/3.52        | ((sk_D) = (k4_relat_1 @ (k4_relat_1 @ sk_D))))),
% 3.34/3.52      inference('demod', [status(thm)], ['243', '250', '251'])).
% 3.34/3.52  thf('253', plain,
% 3.34/3.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.34/3.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.52  thf(t35_funct_2, axiom,
% 3.34/3.52    (![A:$i,B:$i,C:$i]:
% 3.34/3.52     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.34/3.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.34/3.52       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 3.34/3.52         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.34/3.52           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 3.34/3.52             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 3.34/3.52  thf('254', plain,
% 3.34/3.52      (![X52 : $i, X53 : $i, X54 : $i]:
% 3.34/3.52         (((X52) = (k1_xboole_0))
% 3.34/3.52          | ~ (v1_funct_1 @ X53)
% 3.34/3.52          | ~ (v1_funct_2 @ X53 @ X54 @ X52)
% 3.34/3.52          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X52)))
% 3.34/3.52          | ((k5_relat_1 @ X53 @ (k2_funct_1 @ X53)) = (k6_partfun1 @ X54))
% 3.34/3.52          | ~ (v2_funct_1 @ X53)
% 3.34/3.52          | ((k2_relset_1 @ X54 @ X52 @ X53) != (X52)))),
% 3.34/3.52      inference('cnf', [status(esa)], [t35_funct_2])).
% 3.34/3.52  thf('255', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 3.34/3.52      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.34/3.52  thf('256', plain,
% 3.34/3.52      (![X52 : $i, X53 : $i, X54 : $i]:
% 3.34/3.52         (((X52) = (k1_xboole_0))
% 3.34/3.52          | ~ (v1_funct_1 @ X53)
% 3.34/3.52          | ~ (v1_funct_2 @ X53 @ X54 @ X52)
% 3.34/3.52          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X52)))
% 3.34/3.52          | ((k5_relat_1 @ X53 @ (k2_funct_1 @ X53)) = (k6_relat_1 @ X54))
% 3.34/3.52          | ~ (v2_funct_1 @ X53)
% 3.34/3.52          | ((k2_relset_1 @ X54 @ X52 @ X53) != (X52)))),
% 3.34/3.52      inference('demod', [status(thm)], ['254', '255'])).
% 3.34/3.53  thf('257', plain,
% 3.34/3.53      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 3.34/3.53        | ~ (v2_funct_1 @ sk_D)
% 3.34/3.53        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 3.34/3.53        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.34/3.53        | ~ (v1_funct_1 @ sk_D)
% 3.34/3.53        | ((sk_A) = (k1_xboole_0)))),
% 3.34/3.53      inference('sup-', [status(thm)], ['253', '256'])).
% 3.34/3.53  thf('258', plain,
% 3.34/3.53      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 3.34/3.53      inference('sup-', [status(thm)], ['76', '77'])).
% 3.34/3.53  thf('259', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.34/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.53  thf('260', plain, ((v1_funct_1 @ sk_D)),
% 3.34/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.53  thf('261', plain,
% 3.34/3.53      ((((k2_relat_1 @ sk_D) != (sk_A))
% 3.34/3.53        | ~ (v2_funct_1 @ sk_D)
% 3.34/3.53        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 3.34/3.53        | ((sk_A) = (k1_xboole_0)))),
% 3.34/3.53      inference('demod', [status(thm)], ['257', '258', '259', '260'])).
% 3.34/3.53  thf('262', plain, (((sk_A) != (k1_xboole_0))),
% 3.34/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.53  thf('263', plain,
% 3.34/3.53      ((((k2_relat_1 @ sk_D) != (sk_A))
% 3.34/3.53        | ~ (v2_funct_1 @ sk_D)
% 3.34/3.53        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B)))),
% 3.34/3.53      inference('simplify_reflect-', [status(thm)], ['261', '262'])).
% 3.34/3.53  thf('264', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.34/3.53      inference('demod', [status(thm)], ['71', '75', '78', '79', '80', '81'])).
% 3.34/3.53  thf('265', plain,
% 3.34/3.53      ((((sk_A) != (sk_A))
% 3.34/3.53        | ~ (v2_funct_1 @ sk_D)
% 3.34/3.53        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B)))),
% 3.34/3.53      inference('demod', [status(thm)], ['263', '264'])).
% 3.34/3.53  thf('266', plain,
% 3.34/3.53      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 3.34/3.53        | ~ (v2_funct_1 @ sk_D))),
% 3.34/3.53      inference('simplify', [status(thm)], ['265'])).
% 3.34/3.53  thf('267', plain, ((v2_funct_1 @ sk_D)),
% 3.34/3.53      inference('sup-', [status(thm)], ['128', '129'])).
% 3.34/3.53  thf('268', plain,
% 3.34/3.53      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 3.34/3.53      inference('demod', [status(thm)], ['266', '267'])).
% 3.34/3.53  thf('269', plain, (((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))),
% 3.34/3.53      inference('demod', [status(thm)], ['248', '249'])).
% 3.34/3.53  thf('270', plain,
% 3.34/3.53      (((k5_relat_1 @ sk_D @ (k4_relat_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 3.34/3.53      inference('demod', [status(thm)], ['268', '269'])).
% 3.34/3.53  thf('271', plain,
% 3.34/3.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.34/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.53  thf('272', plain,
% 3.34/3.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.34/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.53  thf(redefinition_k1_partfun1, axiom,
% 3.34/3.53    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.34/3.53     ( ( ( v1_funct_1 @ E ) & 
% 3.34/3.53         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.34/3.53         ( v1_funct_1 @ F ) & 
% 3.34/3.53         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.34/3.53       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 3.34/3.53  thf('273', plain,
% 3.34/3.53      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 3.34/3.53         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 3.34/3.53          | ~ (v1_funct_1 @ X32)
% 3.34/3.53          | ~ (v1_funct_1 @ X35)
% 3.34/3.53          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 3.34/3.53          | ((k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35)
% 3.34/3.53              = (k5_relat_1 @ X32 @ X35)))),
% 3.34/3.53      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 3.34/3.53  thf('274', plain,
% 3.34/3.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.34/3.53         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 3.34/3.53            = (k5_relat_1 @ sk_C @ X0))
% 3.34/3.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.34/3.53          | ~ (v1_funct_1 @ X0)
% 3.34/3.53          | ~ (v1_funct_1 @ sk_C))),
% 3.34/3.53      inference('sup-', [status(thm)], ['272', '273'])).
% 3.34/3.53  thf('275', plain, ((v1_funct_1 @ sk_C)),
% 3.34/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.53  thf('276', plain,
% 3.34/3.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.34/3.53         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 3.34/3.53            = (k5_relat_1 @ sk_C @ X0))
% 3.34/3.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.34/3.53          | ~ (v1_funct_1 @ X0))),
% 3.34/3.53      inference('demod', [status(thm)], ['274', '275'])).
% 3.34/3.53  thf('277', plain,
% 3.34/3.53      ((~ (v1_funct_1 @ sk_D)
% 3.34/3.53        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.34/3.53            = (k5_relat_1 @ sk_C @ sk_D)))),
% 3.34/3.53      inference('sup-', [status(thm)], ['271', '276'])).
% 3.34/3.53  thf('278', plain, ((v1_funct_1 @ sk_D)),
% 3.34/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.53  thf('279', plain,
% 3.34/3.53      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.34/3.53         = (k6_relat_1 @ sk_A))),
% 3.34/3.53      inference('demod', [status(thm)], ['58', '61'])).
% 3.34/3.53  thf('280', plain, (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 3.34/3.53      inference('demod', [status(thm)], ['277', '278', '279'])).
% 3.34/3.53  thf('281', plain,
% 3.34/3.53      (![X2 : $i, X3 : $i, X4 : $i]:
% 3.34/3.53         (~ (v1_relat_1 @ X2)
% 3.34/3.53          | ((k5_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 3.34/3.53              = (k5_relat_1 @ X3 @ (k5_relat_1 @ X2 @ X4)))
% 3.34/3.53          | ~ (v1_relat_1 @ X4)
% 3.34/3.53          | ~ (v1_relat_1 @ X3))),
% 3.34/3.53      inference('cnf', [status(esa)], [t55_relat_1])).
% 3.34/3.53  thf('282', plain,
% 3.34/3.53      (![X0 : $i]:
% 3.34/3.53         (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ X0)
% 3.34/3.53            = (k5_relat_1 @ sk_C @ (k5_relat_1 @ sk_D @ X0)))
% 3.34/3.53          | ~ (v1_relat_1 @ sk_C)
% 3.34/3.53          | ~ (v1_relat_1 @ X0)
% 3.34/3.53          | ~ (v1_relat_1 @ sk_D))),
% 3.34/3.53      inference('sup+', [status(thm)], ['280', '281'])).
% 3.34/3.53  thf('283', plain,
% 3.34/3.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.34/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.53  thf('284', plain,
% 3.34/3.53      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.34/3.53         ((v1_relat_1 @ X14)
% 3.34/3.53          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 3.34/3.53      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.34/3.53  thf('285', plain, ((v1_relat_1 @ sk_C)),
% 3.34/3.53      inference('sup-', [status(thm)], ['283', '284'])).
% 3.34/3.53  thf('286', plain, ((v1_relat_1 @ sk_D)),
% 3.34/3.53      inference('sup-', [status(thm)], ['85', '86'])).
% 3.34/3.53  thf('287', plain,
% 3.34/3.53      (![X0 : $i]:
% 3.34/3.53         (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ X0)
% 3.34/3.53            = (k5_relat_1 @ sk_C @ (k5_relat_1 @ sk_D @ X0)))
% 3.34/3.53          | ~ (v1_relat_1 @ X0))),
% 3.34/3.53      inference('demod', [status(thm)], ['282', '285', '286'])).
% 3.34/3.53  thf('288', plain,
% 3.34/3.53      ((((k5_relat_1 @ (k6_relat_1 @ sk_A) @ (k4_relat_1 @ sk_D))
% 3.34/3.53          = (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)))
% 3.34/3.53        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_D)))),
% 3.34/3.53      inference('sup+', [status(thm)], ['270', '287'])).
% 3.34/3.53  thf(dt_k4_relat_1, axiom,
% 3.34/3.53    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 3.34/3.53  thf('289', plain,
% 3.34/3.53      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 3.34/3.53      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 3.34/3.53  thf('290', plain,
% 3.34/3.53      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 3.34/3.53      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 3.34/3.53  thf('291', plain, ((v1_relat_1 @ sk_D)),
% 3.34/3.53      inference('sup-', [status(thm)], ['85', '86'])).
% 3.34/3.53  thf('292', plain,
% 3.34/3.53      (![X1 : $i]:
% 3.34/3.53         (((k2_relat_1 @ X1) = (k1_relat_1 @ (k4_relat_1 @ X1)))
% 3.34/3.53          | ~ (v1_relat_1 @ X1))),
% 3.34/3.53      inference('cnf', [status(esa)], [t37_relat_1])).
% 3.34/3.53  thf('293', plain,
% 3.34/3.53      (((k2_relat_1 @ sk_D) = (k1_relat_1 @ (k4_relat_1 @ sk_D)))),
% 3.34/3.53      inference('sup-', [status(thm)], ['291', '292'])).
% 3.34/3.53  thf('294', plain,
% 3.34/3.53      (![X8 : $i]:
% 3.34/3.53         (((k7_relat_1 @ X8 @ (k1_relat_1 @ X8)) = (X8)) | ~ (v1_relat_1 @ X8))),
% 3.34/3.53      inference('cnf', [status(esa)], [t98_relat_1])).
% 3.34/3.53  thf('295', plain,
% 3.34/3.53      ((((k7_relat_1 @ (k4_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D))
% 3.34/3.53          = (k4_relat_1 @ sk_D))
% 3.34/3.53        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_D)))),
% 3.34/3.53      inference('sup+', [status(thm)], ['293', '294'])).
% 3.34/3.53  thf('296', plain,
% 3.34/3.53      ((~ (v1_relat_1 @ sk_D)
% 3.34/3.53        | ((k7_relat_1 @ (k4_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D))
% 3.34/3.53            = (k4_relat_1 @ sk_D)))),
% 3.34/3.53      inference('sup-', [status(thm)], ['290', '295'])).
% 3.34/3.53  thf('297', plain, ((v1_relat_1 @ sk_D)),
% 3.34/3.53      inference('sup-', [status(thm)], ['85', '86'])).
% 3.34/3.53  thf('298', plain,
% 3.34/3.53      (((k7_relat_1 @ (k4_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D))
% 3.34/3.53         = (k4_relat_1 @ sk_D))),
% 3.34/3.53      inference('demod', [status(thm)], ['296', '297'])).
% 3.34/3.53  thf('299', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.34/3.53      inference('demod', [status(thm)], ['71', '75', '78', '79', '80', '81'])).
% 3.34/3.53  thf('300', plain,
% 3.34/3.53      (((k7_relat_1 @ (k4_relat_1 @ sk_D) @ sk_A) = (k4_relat_1 @ sk_D))),
% 3.34/3.53      inference('demod', [status(thm)], ['298', '299'])).
% 3.34/3.53  thf('301', plain,
% 3.34/3.53      (![X6 : $i, X7 : $i]:
% 3.34/3.53         (((k7_relat_1 @ X7 @ X6) = (k5_relat_1 @ (k6_relat_1 @ X6) @ X7))
% 3.34/3.53          | ~ (v1_relat_1 @ X7))),
% 3.34/3.53      inference('cnf', [status(esa)], [t94_relat_1])).
% 3.34/3.53  thf('302', plain,
% 3.34/3.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.34/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.53  thf('303', plain,
% 3.34/3.53      (![X52 : $i, X53 : $i, X54 : $i]:
% 3.34/3.53         (((X52) = (k1_xboole_0))
% 3.34/3.53          | ~ (v1_funct_1 @ X53)
% 3.34/3.53          | ~ (v1_funct_2 @ X53 @ X54 @ X52)
% 3.34/3.53          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X52)))
% 3.34/3.53          | ((k5_relat_1 @ X53 @ (k2_funct_1 @ X53)) = (k6_relat_1 @ X54))
% 3.34/3.53          | ~ (v2_funct_1 @ X53)
% 3.34/3.53          | ((k2_relset_1 @ X54 @ X52 @ X53) != (X52)))),
% 3.34/3.53      inference('demod', [status(thm)], ['254', '255'])).
% 3.34/3.53  thf('304', plain,
% 3.34/3.53      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 3.34/3.53        | ~ (v2_funct_1 @ sk_C)
% 3.34/3.53        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 3.34/3.53        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.34/3.53        | ~ (v1_funct_1 @ sk_C)
% 3.34/3.53        | ((sk_B) = (k1_xboole_0)))),
% 3.34/3.53      inference('sup-', [status(thm)], ['302', '303'])).
% 3.34/3.53  thf('305', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 3.34/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.53  thf('306', plain, ((v2_funct_1 @ sk_C)),
% 3.34/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.53  thf('307', plain, ((v1_funct_1 @ sk_C)),
% 3.34/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.53  thf('308', plain,
% 3.34/3.53      (![X9 : $i]:
% 3.34/3.53         (~ (v2_funct_1 @ X9)
% 3.34/3.53          | ((k2_funct_1 @ X9) = (k4_relat_1 @ X9))
% 3.34/3.53          | ~ (v1_funct_1 @ X9)
% 3.34/3.53          | ~ (v1_relat_1 @ X9))),
% 3.34/3.53      inference('cnf', [status(esa)], [d9_funct_1])).
% 3.34/3.53  thf('309', plain,
% 3.34/3.53      ((~ (v1_relat_1 @ sk_C)
% 3.34/3.53        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 3.34/3.53        | ~ (v2_funct_1 @ sk_C))),
% 3.34/3.53      inference('sup-', [status(thm)], ['307', '308'])).
% 3.34/3.53  thf('310', plain, ((v1_relat_1 @ sk_C)),
% 3.34/3.53      inference('sup-', [status(thm)], ['283', '284'])).
% 3.34/3.53  thf('311', plain, ((v2_funct_1 @ sk_C)),
% 3.34/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.53  thf('312', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 3.34/3.53      inference('demod', [status(thm)], ['309', '310', '311'])).
% 3.34/3.53  thf('313', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.34/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.53  thf('314', plain, ((v1_funct_1 @ sk_C)),
% 3.34/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.53  thf('315', plain,
% 3.34/3.53      ((((sk_B) != (sk_B))
% 3.34/3.53        | ((k5_relat_1 @ sk_C @ (k4_relat_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 3.34/3.53        | ((sk_B) = (k1_xboole_0)))),
% 3.34/3.53      inference('demod', [status(thm)],
% 3.34/3.53                ['304', '305', '306', '312', '313', '314'])).
% 3.34/3.53  thf('316', plain,
% 3.34/3.53      ((((sk_B) = (k1_xboole_0))
% 3.34/3.53        | ((k5_relat_1 @ sk_C @ (k4_relat_1 @ sk_C)) = (k6_relat_1 @ sk_A)))),
% 3.34/3.53      inference('simplify', [status(thm)], ['315'])).
% 3.34/3.53  thf('317', plain, (((sk_B) != (k1_xboole_0))),
% 3.34/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.53  thf('318', plain,
% 3.34/3.53      (((k5_relat_1 @ sk_C @ (k4_relat_1 @ sk_C)) = (k6_relat_1 @ sk_A))),
% 3.34/3.53      inference('simplify_reflect-', [status(thm)], ['316', '317'])).
% 3.34/3.53  thf('319', plain,
% 3.34/3.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.34/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.53  thf('320', plain,
% 3.34/3.53      (![X52 : $i, X53 : $i, X54 : $i]:
% 3.34/3.53         (((X52) = (k1_xboole_0))
% 3.34/3.53          | ~ (v1_funct_1 @ X53)
% 3.34/3.53          | ~ (v1_funct_2 @ X53 @ X54 @ X52)
% 3.34/3.53          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X52)))
% 3.34/3.53          | ((k5_relat_1 @ (k2_funct_1 @ X53) @ X53) = (k6_partfun1 @ X52))
% 3.34/3.53          | ~ (v2_funct_1 @ X53)
% 3.34/3.53          | ((k2_relset_1 @ X54 @ X52 @ X53) != (X52)))),
% 3.34/3.53      inference('cnf', [status(esa)], [t35_funct_2])).
% 3.34/3.53  thf('321', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 3.34/3.53      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.34/3.53  thf('322', plain,
% 3.34/3.53      (![X52 : $i, X53 : $i, X54 : $i]:
% 3.34/3.53         (((X52) = (k1_xboole_0))
% 3.34/3.53          | ~ (v1_funct_1 @ X53)
% 3.34/3.53          | ~ (v1_funct_2 @ X53 @ X54 @ X52)
% 3.34/3.53          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X52)))
% 3.34/3.53          | ((k5_relat_1 @ (k2_funct_1 @ X53) @ X53) = (k6_relat_1 @ X52))
% 3.34/3.53          | ~ (v2_funct_1 @ X53)
% 3.34/3.53          | ((k2_relset_1 @ X54 @ X52 @ X53) != (X52)))),
% 3.34/3.53      inference('demod', [status(thm)], ['320', '321'])).
% 3.34/3.53  thf('323', plain,
% 3.34/3.53      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 3.34/3.53        | ~ (v2_funct_1 @ sk_C)
% 3.34/3.53        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))
% 3.34/3.53        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.34/3.53        | ~ (v1_funct_1 @ sk_C)
% 3.34/3.53        | ((sk_B) = (k1_xboole_0)))),
% 3.34/3.53      inference('sup-', [status(thm)], ['319', '322'])).
% 3.34/3.53  thf('324', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 3.34/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.53  thf('325', plain, ((v2_funct_1 @ sk_C)),
% 3.34/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.53  thf('326', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 3.34/3.53      inference('demod', [status(thm)], ['309', '310', '311'])).
% 3.34/3.53  thf('327', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.34/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.53  thf('328', plain, ((v1_funct_1 @ sk_C)),
% 3.34/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.53  thf('329', plain,
% 3.34/3.53      ((((sk_B) != (sk_B))
% 3.34/3.53        | ((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))
% 3.34/3.53        | ((sk_B) = (k1_xboole_0)))),
% 3.34/3.53      inference('demod', [status(thm)],
% 3.34/3.53                ['323', '324', '325', '326', '327', '328'])).
% 3.34/3.53  thf('330', plain,
% 3.34/3.53      ((((sk_B) = (k1_xboole_0))
% 3.34/3.53        | ((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B)))),
% 3.34/3.53      inference('simplify', [status(thm)], ['329'])).
% 3.34/3.53  thf('331', plain, (((sk_B) != (k1_xboole_0))),
% 3.34/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.53  thf('332', plain,
% 3.34/3.53      (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))),
% 3.34/3.53      inference('simplify_reflect-', [status(thm)], ['330', '331'])).
% 3.34/3.53  thf('333', plain,
% 3.34/3.53      (((k5_relat_1 @ sk_C @ (k4_relat_1 @ sk_C)) = (k6_relat_1 @ sk_A))),
% 3.34/3.53      inference('simplify_reflect-', [status(thm)], ['316', '317'])).
% 3.34/3.53  thf('334', plain,
% 3.34/3.53      (![X2 : $i, X3 : $i, X4 : $i]:
% 3.34/3.53         (~ (v1_relat_1 @ X2)
% 3.34/3.53          | ((k5_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 3.34/3.53              = (k5_relat_1 @ X3 @ (k5_relat_1 @ X2 @ X4)))
% 3.34/3.53          | ~ (v1_relat_1 @ X4)
% 3.34/3.53          | ~ (v1_relat_1 @ X3))),
% 3.34/3.53      inference('cnf', [status(esa)], [t55_relat_1])).
% 3.34/3.53  thf('335', plain,
% 3.34/3.53      (![X0 : $i]:
% 3.34/3.53         (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ X0)
% 3.34/3.53            = (k5_relat_1 @ sk_C @ (k5_relat_1 @ (k4_relat_1 @ sk_C) @ X0)))
% 3.34/3.53          | ~ (v1_relat_1 @ sk_C)
% 3.34/3.53          | ~ (v1_relat_1 @ X0)
% 3.34/3.53          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 3.34/3.53      inference('sup+', [status(thm)], ['333', '334'])).
% 3.34/3.53  thf('336', plain, ((v1_relat_1 @ sk_C)),
% 3.34/3.53      inference('sup-', [status(thm)], ['283', '284'])).
% 3.34/3.53  thf('337', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 3.34/3.53      inference('demod', [status(thm)], ['309', '310', '311'])).
% 3.34/3.53  thf('338', plain,
% 3.34/3.53      (![X10 : $i]:
% 3.34/3.53         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 3.34/3.53          | ~ (v1_funct_1 @ X10)
% 3.34/3.53          | ~ (v1_relat_1 @ X10))),
% 3.34/3.53      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.34/3.53  thf('339', plain,
% 3.34/3.53      (((v1_relat_1 @ (k4_relat_1 @ sk_C))
% 3.34/3.53        | ~ (v1_relat_1 @ sk_C)
% 3.34/3.53        | ~ (v1_funct_1 @ sk_C))),
% 3.34/3.53      inference('sup+', [status(thm)], ['337', '338'])).
% 3.34/3.53  thf('340', plain, ((v1_relat_1 @ sk_C)),
% 3.34/3.53      inference('sup-', [status(thm)], ['283', '284'])).
% 3.34/3.53  thf('341', plain, ((v1_funct_1 @ sk_C)),
% 3.34/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.53  thf('342', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 3.34/3.53      inference('demod', [status(thm)], ['339', '340', '341'])).
% 3.34/3.53  thf('343', plain,
% 3.34/3.53      (![X0 : $i]:
% 3.34/3.53         (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ X0)
% 3.34/3.53            = (k5_relat_1 @ sk_C @ (k5_relat_1 @ (k4_relat_1 @ sk_C) @ X0)))
% 3.34/3.53          | ~ (v1_relat_1 @ X0))),
% 3.34/3.53      inference('demod', [status(thm)], ['335', '336', '342'])).
% 3.34/3.53  thf('344', plain,
% 3.34/3.53      ((((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_C)
% 3.34/3.53          = (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)))
% 3.34/3.53        | ~ (v1_relat_1 @ sk_C))),
% 3.34/3.53      inference('sup+', [status(thm)], ['332', '343'])).
% 3.34/3.53  thf('345', plain,
% 3.34/3.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.34/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.53  thf('346', plain,
% 3.34/3.53      (![X17 : $i, X18 : $i, X19 : $i]:
% 3.34/3.53         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 3.34/3.53          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 3.34/3.53      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.34/3.53  thf('347', plain,
% 3.34/3.53      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 3.34/3.53      inference('sup-', [status(thm)], ['345', '346'])).
% 3.34/3.53  thf('348', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 3.34/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.53  thf('349', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 3.34/3.53      inference('sup+', [status(thm)], ['347', '348'])).
% 3.34/3.53  thf('350', plain,
% 3.34/3.53      (![X5 : $i]:
% 3.34/3.53         (((k5_relat_1 @ X5 @ (k6_relat_1 @ (k2_relat_1 @ X5))) = (X5))
% 3.34/3.53          | ~ (v1_relat_1 @ X5))),
% 3.34/3.53      inference('cnf', [status(esa)], [t80_relat_1])).
% 3.34/3.53  thf('351', plain,
% 3.34/3.53      ((((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) = (sk_C))
% 3.34/3.53        | ~ (v1_relat_1 @ sk_C))),
% 3.34/3.53      inference('sup+', [status(thm)], ['349', '350'])).
% 3.34/3.53  thf('352', plain, ((v1_relat_1 @ sk_C)),
% 3.34/3.53      inference('sup-', [status(thm)], ['283', '284'])).
% 3.34/3.53  thf('353', plain, (((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) = (sk_C))),
% 3.34/3.53      inference('demod', [status(thm)], ['351', '352'])).
% 3.34/3.53  thf('354', plain, ((v1_relat_1 @ sk_C)),
% 3.34/3.53      inference('sup-', [status(thm)], ['283', '284'])).
% 3.34/3.53  thf('355', plain, (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_C) = (sk_C))),
% 3.34/3.53      inference('demod', [status(thm)], ['344', '353', '354'])).
% 3.34/3.53  thf('356', plain,
% 3.34/3.53      (![X2 : $i, X3 : $i, X4 : $i]:
% 3.34/3.53         (~ (v1_relat_1 @ X2)
% 3.34/3.53          | ((k5_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 3.34/3.53              = (k5_relat_1 @ X3 @ (k5_relat_1 @ X2 @ X4)))
% 3.34/3.53          | ~ (v1_relat_1 @ X4)
% 3.34/3.53          | ~ (v1_relat_1 @ X3))),
% 3.34/3.53      inference('cnf', [status(esa)], [t55_relat_1])).
% 3.34/3.53  thf('357', plain,
% 3.34/3.53      (![X0 : $i]:
% 3.34/3.53         (((k5_relat_1 @ sk_C @ X0)
% 3.34/3.53            = (k5_relat_1 @ (k6_relat_1 @ sk_A) @ (k5_relat_1 @ sk_C @ X0)))
% 3.34/3.53          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A))
% 3.34/3.53          | ~ (v1_relat_1 @ X0)
% 3.34/3.53          | ~ (v1_relat_1 @ sk_C))),
% 3.34/3.53      inference('sup+', [status(thm)], ['355', '356'])).
% 3.34/3.53  thf('358', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 3.34/3.53      inference('cnf', [status(esa)], [fc4_funct_1])).
% 3.34/3.53  thf('359', plain, ((v1_relat_1 @ sk_C)),
% 3.34/3.53      inference('sup-', [status(thm)], ['283', '284'])).
% 3.34/3.53  thf('360', plain,
% 3.34/3.53      (![X0 : $i]:
% 3.34/3.53         (((k5_relat_1 @ sk_C @ X0)
% 3.34/3.53            = (k5_relat_1 @ (k6_relat_1 @ sk_A) @ (k5_relat_1 @ sk_C @ X0)))
% 3.34/3.53          | ~ (v1_relat_1 @ X0))),
% 3.34/3.53      inference('demod', [status(thm)], ['357', '358', '359'])).
% 3.34/3.53  thf('361', plain,
% 3.34/3.53      ((((k5_relat_1 @ sk_C @ (k4_relat_1 @ sk_C))
% 3.34/3.53          = (k5_relat_1 @ (k6_relat_1 @ sk_A) @ (k6_relat_1 @ sk_A)))
% 3.34/3.53        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 3.34/3.53      inference('sup+', [status(thm)], ['318', '360'])).
% 3.34/3.53  thf('362', plain,
% 3.34/3.53      (((k5_relat_1 @ sk_C @ (k4_relat_1 @ sk_C)) = (k6_relat_1 @ sk_A))),
% 3.34/3.53      inference('simplify_reflect-', [status(thm)], ['316', '317'])).
% 3.34/3.53  thf('363', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 3.34/3.53      inference('demod', [status(thm)], ['339', '340', '341'])).
% 3.34/3.53  thf('364', plain,
% 3.34/3.53      (((k6_relat_1 @ sk_A)
% 3.34/3.53         = (k5_relat_1 @ (k6_relat_1 @ sk_A) @ (k6_relat_1 @ sk_A)))),
% 3.34/3.53      inference('demod', [status(thm)], ['361', '362', '363'])).
% 3.34/3.53  thf('365', plain,
% 3.34/3.53      (![X2 : $i, X3 : $i, X4 : $i]:
% 3.34/3.53         (~ (v1_relat_1 @ X2)
% 3.34/3.53          | ((k5_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 3.34/3.53              = (k5_relat_1 @ X3 @ (k5_relat_1 @ X2 @ X4)))
% 3.34/3.53          | ~ (v1_relat_1 @ X4)
% 3.34/3.53          | ~ (v1_relat_1 @ X3))),
% 3.34/3.53      inference('cnf', [status(esa)], [t55_relat_1])).
% 3.34/3.53  thf('366', plain,
% 3.34/3.53      (![X0 : $i]:
% 3.34/3.53         (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ X0)
% 3.34/3.53            = (k5_relat_1 @ (k6_relat_1 @ sk_A) @ 
% 3.34/3.53               (k5_relat_1 @ (k6_relat_1 @ sk_A) @ X0)))
% 3.34/3.53          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A))
% 3.34/3.53          | ~ (v1_relat_1 @ X0)
% 3.34/3.53          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 3.34/3.53      inference('sup+', [status(thm)], ['364', '365'])).
% 3.34/3.53  thf('367', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 3.34/3.53      inference('cnf', [status(esa)], [fc4_funct_1])).
% 3.34/3.53  thf('368', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 3.34/3.53      inference('cnf', [status(esa)], [fc4_funct_1])).
% 3.34/3.53  thf('369', plain,
% 3.34/3.53      (![X0 : $i]:
% 3.34/3.53         (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ X0)
% 3.34/3.53            = (k5_relat_1 @ (k6_relat_1 @ sk_A) @ 
% 3.34/3.53               (k5_relat_1 @ (k6_relat_1 @ sk_A) @ X0)))
% 3.34/3.53          | ~ (v1_relat_1 @ X0))),
% 3.34/3.53      inference('demod', [status(thm)], ['366', '367', '368'])).
% 3.34/3.53  thf('370', plain,
% 3.34/3.53      (![X0 : $i]:
% 3.34/3.53         (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ X0)
% 3.34/3.53            = (k5_relat_1 @ (k6_relat_1 @ sk_A) @ (k7_relat_1 @ X0 @ sk_A)))
% 3.34/3.53          | ~ (v1_relat_1 @ X0)
% 3.34/3.53          | ~ (v1_relat_1 @ X0))),
% 3.34/3.53      inference('sup+', [status(thm)], ['301', '369'])).
% 3.34/3.53  thf('371', plain,
% 3.34/3.53      (![X0 : $i]:
% 3.34/3.53         (~ (v1_relat_1 @ X0)
% 3.34/3.53          | ((k5_relat_1 @ (k6_relat_1 @ sk_A) @ X0)
% 3.34/3.53              = (k5_relat_1 @ (k6_relat_1 @ sk_A) @ (k7_relat_1 @ X0 @ sk_A))))),
% 3.34/3.53      inference('simplify', [status(thm)], ['370'])).
% 3.34/3.53  thf('372', plain,
% 3.34/3.53      (![X6 : $i, X7 : $i]:
% 3.34/3.53         (((k7_relat_1 @ X7 @ X6) = (k5_relat_1 @ (k6_relat_1 @ X6) @ X7))
% 3.34/3.53          | ~ (v1_relat_1 @ X7))),
% 3.34/3.53      inference('cnf', [status(esa)], [t94_relat_1])).
% 3.34/3.53  thf('373', plain,
% 3.34/3.53      (![X0 : $i]:
% 3.34/3.53         (((k7_relat_1 @ (k7_relat_1 @ X0 @ sk_A) @ sk_A)
% 3.34/3.53            = (k5_relat_1 @ (k6_relat_1 @ sk_A) @ X0))
% 3.34/3.53          | ~ (v1_relat_1 @ X0)
% 3.34/3.53          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ sk_A)))),
% 3.34/3.53      inference('sup+', [status(thm)], ['371', '372'])).
% 3.34/3.53  thf('374', plain,
% 3.34/3.53      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_D))
% 3.34/3.53        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_D))
% 3.34/3.53        | ((k7_relat_1 @ (k7_relat_1 @ (k4_relat_1 @ sk_D) @ sk_A) @ sk_A)
% 3.34/3.53            = (k5_relat_1 @ (k6_relat_1 @ sk_A) @ (k4_relat_1 @ sk_D))))),
% 3.34/3.53      inference('sup-', [status(thm)], ['300', '373'])).
% 3.34/3.53  thf('375', plain,
% 3.34/3.53      (((k7_relat_1 @ (k4_relat_1 @ sk_D) @ sk_A) = (k4_relat_1 @ sk_D))),
% 3.34/3.53      inference('demod', [status(thm)], ['298', '299'])).
% 3.34/3.53  thf('376', plain,
% 3.34/3.53      (((k7_relat_1 @ (k4_relat_1 @ sk_D) @ sk_A) = (k4_relat_1 @ sk_D))),
% 3.34/3.53      inference('demod', [status(thm)], ['298', '299'])).
% 3.34/3.53  thf('377', plain,
% 3.34/3.53      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_D))
% 3.34/3.53        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_D))
% 3.34/3.53        | ((k4_relat_1 @ sk_D)
% 3.34/3.53            = (k5_relat_1 @ (k6_relat_1 @ sk_A) @ (k4_relat_1 @ sk_D))))),
% 3.34/3.53      inference('demod', [status(thm)], ['374', '375', '376'])).
% 3.34/3.53  thf('378', plain,
% 3.34/3.53      ((((k4_relat_1 @ sk_D)
% 3.34/3.53          = (k5_relat_1 @ (k6_relat_1 @ sk_A) @ (k4_relat_1 @ sk_D)))
% 3.34/3.53        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_D)))),
% 3.34/3.53      inference('simplify', [status(thm)], ['377'])).
% 3.34/3.53  thf('379', plain,
% 3.34/3.53      ((~ (v1_relat_1 @ sk_D)
% 3.34/3.53        | ((k4_relat_1 @ sk_D)
% 3.34/3.53            = (k5_relat_1 @ (k6_relat_1 @ sk_A) @ (k4_relat_1 @ sk_D))))),
% 3.34/3.53      inference('sup-', [status(thm)], ['289', '378'])).
% 3.34/3.53  thf('380', plain, ((v1_relat_1 @ sk_D)),
% 3.34/3.53      inference('sup-', [status(thm)], ['85', '86'])).
% 3.34/3.53  thf('381', plain,
% 3.34/3.53      (((k4_relat_1 @ sk_D)
% 3.34/3.53         = (k5_relat_1 @ (k6_relat_1 @ sk_A) @ (k4_relat_1 @ sk_D)))),
% 3.34/3.53      inference('demod', [status(thm)], ['379', '380'])).
% 3.34/3.53  thf('382', plain, (((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) = (sk_C))),
% 3.34/3.53      inference('demod', [status(thm)], ['351', '352'])).
% 3.34/3.53  thf('383', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))),
% 3.34/3.53      inference('demod', [status(thm)], ['103', '104'])).
% 3.34/3.53  thf('384', plain,
% 3.34/3.53      (![X0 : $i]:
% 3.34/3.53         (~ (v2_funct_1 @ X0)
% 3.34/3.53          | ~ (v1_funct_1 @ X0)
% 3.34/3.53          | ~ (v1_relat_1 @ X0)
% 3.34/3.53          | (v1_relat_1 @ (k2_funct_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)))))),
% 3.34/3.53      inference('simplify', [status(thm)], ['213'])).
% 3.34/3.53  thf('385', plain,
% 3.34/3.53      (((v1_relat_1 @ (k2_funct_1 @ sk_D))
% 3.34/3.53        | ~ (v1_relat_1 @ sk_D)
% 3.34/3.53        | ~ (v1_funct_1 @ sk_D)
% 3.34/3.53        | ~ (v2_funct_1 @ sk_D))),
% 3.34/3.53      inference('sup+', [status(thm)], ['383', '384'])).
% 3.34/3.53  thf('386', plain, ((v1_relat_1 @ sk_D)),
% 3.34/3.53      inference('sup-', [status(thm)], ['85', '86'])).
% 3.34/3.53  thf('387', plain, ((v1_funct_1 @ sk_D)),
% 3.34/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.53  thf('388', plain,
% 3.34/3.53      (((v1_relat_1 @ (k2_funct_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 3.34/3.53      inference('demod', [status(thm)], ['385', '386', '387'])).
% 3.34/3.53  thf('389', plain, ((v2_funct_1 @ sk_D)),
% 3.34/3.53      inference('sup-', [status(thm)], ['128', '129'])).
% 3.34/3.53  thf('390', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_D))),
% 3.34/3.53      inference('demod', [status(thm)], ['388', '389'])).
% 3.34/3.53  thf('391', plain, (((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))),
% 3.34/3.53      inference('demod', [status(thm)], ['248', '249'])).
% 3.34/3.53  thf('392', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_D))),
% 3.34/3.53      inference('demod', [status(thm)], ['390', '391'])).
% 3.34/3.53  thf('393', plain, (((k4_relat_1 @ sk_D) = (sk_C))),
% 3.34/3.53      inference('demod', [status(thm)], ['288', '381', '382', '392'])).
% 3.34/3.53  thf('394', plain, ((v2_funct_1 @ sk_C)),
% 3.34/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.53  thf('395', plain, (((k4_relat_1 @ sk_D) = (sk_C))),
% 3.34/3.53      inference('demod', [status(thm)], ['288', '381', '382', '392'])).
% 3.34/3.53  thf('396', plain, (((sk_D) = (k4_relat_1 @ sk_C))),
% 3.34/3.53      inference('demod', [status(thm)], ['252', '393', '394', '395'])).
% 3.34/3.53  thf('397', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 3.34/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.53  thf('398', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 3.34/3.53      inference('demod', [status(thm)], ['309', '310', '311'])).
% 3.34/3.53  thf('399', plain, (((sk_D) != (k4_relat_1 @ sk_C))),
% 3.34/3.53      inference('demod', [status(thm)], ['397', '398'])).
% 3.34/3.53  thf('400', plain, ($false),
% 3.34/3.53      inference('simplify_reflect-', [status(thm)], ['396', '399'])).
% 3.34/3.53  
% 3.34/3.53  % SZS output end Refutation
% 3.34/3.53  
% 3.34/3.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
