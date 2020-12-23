%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SdglznCM9D

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 128 expanded)
%              Number of leaves         :   27 (  56 expanded)
%              Depth                    :   13
%              Number of atoms          :  590 (1023 expanded)
%              Number of equality atoms :   36 (  60 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k8_relat_1 @ X27 @ X26 )
        = ( k5_relat_1 @ X26 @ ( k6_relat_1 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t43_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_funct_1])).

thf('1',plain,(
    ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
     != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc24_relat_1,axiom,(
    ! [A: $i] :
      ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X48: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('4',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t119_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('5',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X25 @ X24 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X24 ) @ X25 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('6',plain,(
    ! [X46: $i,X47: $i] :
      ( ( ( k7_relat_1 @ X47 @ X46 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X46 ) @ X47 ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('7',plain,(
    ! [X44: $i,X45: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X44 @ ( k6_relat_1 @ X45 ) ) @ X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X48: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('10',plain,(
    ! [X48: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k8_relat_1 @ X27 @ X26 )
        = ( k5_relat_1 @ X26 @ ( k6_relat_1 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('13',plain,(
    ! [X46: $i,X47: $i] :
      ( ( ( k7_relat_1 @ X47 @ X46 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X46 ) @ X47 ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X48: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('16',plain,(
    ! [X48: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','17'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v1_relat_1 @ X37 )
      | ( r1_tarski @ ( k2_relat_1 @ X38 ) @ ( k2_relat_1 @ X37 ) )
      | ~ ( r1_tarski @ X38 @ X37 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X46: $i,X47: $i] :
      ( ( ( k7_relat_1 @ X47 @ X46 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X46 ) @ X47 ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('22',plain,(
    ! [X44: $i,X45: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X44 @ ( k6_relat_1 @ X45 ) ) @ X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X16: $i,X18: $i] :
      ( ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('25',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('30',plain,(
    ! [X48: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('31',plain,(
    ! [X48: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29','30','31'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('33',plain,(
    ! [X42: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('34',plain,(
    ! [X48: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 ) ),
    inference(demod,[status(thm)],['20','32','33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ ( k2_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','35'])).

thf('37',plain,(
    ! [X42: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('38',plain,(
    ! [X48: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ! [X42: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('41',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X28 ) @ X29 )
      | ( ( k8_relat_1 @ X29 @ X28 )
        = X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X48: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf(t192_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('47',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k7_relat_1 @ X33 @ X34 )
        = ( k7_relat_1 @ X33 @ ( k3_xboole_0 @ ( k1_relat_1 @ X33 ) @ X34 ) ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('50',plain,(
    ! [X41: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X41 ) )
      = X41 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('51',plain,(
    ! [X48: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['48','49','50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','52'])).

thf('54',plain,(
    ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','53'])).

thf('55',plain,(
    $false ),
    inference(simplify,[status(thm)],['54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SdglznCM9D
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:43:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 124 iterations in 0.066s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.52  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.52  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.52  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(t123_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ B ) =>
% 0.21/0.52       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      (![X26 : $i, X27 : $i]:
% 0.21/0.52         (((k8_relat_1 @ X27 @ X26) = (k5_relat_1 @ X26 @ (k6_relat_1 @ X27)))
% 0.21/0.52          | ~ (v1_relat_1 @ X26))),
% 0.21/0.52      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.21/0.52  thf(t43_funct_1, conjecture,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.21/0.52       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i,B:$i]:
% 0.21/0.52        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.21/0.52          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.21/0.52         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      ((((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.21/0.52          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 0.21/0.52        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.52  thf(fc24_relat_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.21/0.52       ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.21/0.52       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.21/0.52  thf('3', plain, (![X48 : $i]: (v1_relat_1 @ (k6_relat_1 @ X48))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.21/0.52         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.52  thf(t119_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ B ) =>
% 0.21/0.52       ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) =
% 0.21/0.52         ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (![X24 : $i, X25 : $i]:
% 0.21/0.52         (((k2_relat_1 @ (k8_relat_1 @ X25 @ X24))
% 0.21/0.52            = (k3_xboole_0 @ (k2_relat_1 @ X24) @ X25))
% 0.21/0.52          | ~ (v1_relat_1 @ X24))),
% 0.21/0.52      inference('cnf', [status(esa)], [t119_relat_1])).
% 0.21/0.52  thf(t94_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ B ) =>
% 0.21/0.52       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (![X46 : $i, X47 : $i]:
% 0.21/0.52         (((k7_relat_1 @ X47 @ X46) = (k5_relat_1 @ (k6_relat_1 @ X46) @ X47))
% 0.21/0.52          | ~ (v1_relat_1 @ X47))),
% 0.21/0.52      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.21/0.52  thf(t76_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ B ) =>
% 0.21/0.52       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 0.21/0.52         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X44 : $i, X45 : $i]:
% 0.21/0.52         ((r1_tarski @ (k5_relat_1 @ X44 @ (k6_relat_1 @ X45)) @ X44)
% 0.21/0.52          | ~ (v1_relat_1 @ X44))),
% 0.21/0.52      inference('cnf', [status(esa)], [t76_relat_1])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 0.21/0.52           (k6_relat_1 @ X0))
% 0.21/0.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.21/0.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.52  thf('9', plain, (![X48 : $i]: (v1_relat_1 @ (k6_relat_1 @ X48))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.52  thf('10', plain, (![X48 : $i]: (v1_relat_1 @ (k6_relat_1 @ X48))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ (k6_relat_1 @ X0))),
% 0.21/0.52      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      (![X26 : $i, X27 : $i]:
% 0.21/0.52         (((k8_relat_1 @ X27 @ X26) = (k5_relat_1 @ X26 @ (k6_relat_1 @ X27)))
% 0.21/0.52          | ~ (v1_relat_1 @ X26))),
% 0.21/0.52      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X46 : $i, X47 : $i]:
% 0.21/0.52         (((k7_relat_1 @ X47 @ X46) = (k5_relat_1 @ (k6_relat_1 @ X46) @ X47))
% 0.21/0.52          | ~ (v1_relat_1 @ X47))),
% 0.21/0.52      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.21/0.52            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.21/0.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.52  thf('15', plain, (![X48 : $i]: (v1_relat_1 @ (k6_relat_1 @ X48))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.52  thf('16', plain, (![X48 : $i]: (v1_relat_1 @ (k6_relat_1 @ X48))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.21/0.52           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.21/0.52      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (r1_tarski @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ (k6_relat_1 @ X0))),
% 0.21/0.52      inference('demod', [status(thm)], ['11', '17'])).
% 0.21/0.52  thf(t25_relat_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( v1_relat_1 @ B ) =>
% 0.21/0.52           ( ( r1_tarski @ A @ B ) =>
% 0.21/0.52             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.21/0.52               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (![X37 : $i, X38 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X37)
% 0.21/0.52          | (r1_tarski @ (k2_relat_1 @ X38) @ (k2_relat_1 @ X37))
% 0.21/0.52          | ~ (r1_tarski @ X38 @ X37)
% 0.21/0.52          | ~ (v1_relat_1 @ X38))),
% 0.21/0.52      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.21/0.52          | (r1_tarski @ 
% 0.21/0.52             (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.21/0.52             (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.21/0.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (![X46 : $i, X47 : $i]:
% 0.21/0.52         (((k7_relat_1 @ X47 @ X46) = (k5_relat_1 @ (k6_relat_1 @ X46) @ X47))
% 0.21/0.52          | ~ (v1_relat_1 @ X47))),
% 0.21/0.52      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (![X44 : $i, X45 : $i]:
% 0.21/0.52         ((r1_tarski @ (k5_relat_1 @ X44 @ (k6_relat_1 @ X45)) @ X44)
% 0.21/0.52          | ~ (v1_relat_1 @ X44))),
% 0.21/0.52      inference('cnf', [status(esa)], [t76_relat_1])).
% 0.21/0.52  thf(t3_subset, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      (![X16 : $i, X18 : $i]:
% 0.21/0.52         ((m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X16 @ X18))),
% 0.21/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X0)
% 0.21/0.52          | (m1_subset_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ 
% 0.21/0.52             (k1_zfmisc_1 @ X0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.52  thf(cc2_relat_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      (![X19 : $i, X20 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 0.21/0.52          | (v1_relat_1 @ X19)
% 0.21/0.52          | ~ (v1_relat_1 @ X20))),
% 0.21/0.52      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X0)
% 0.21/0.52          | ~ (v1_relat_1 @ X0)
% 0.21/0.52          | (v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.21/0.52          | ~ (v1_relat_1 @ X0))),
% 0.21/0.52      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.21/0.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.21/0.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['21', '27'])).
% 0.21/0.52  thf('29', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.21/0.52           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.21/0.52      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.21/0.52  thf('30', plain, (![X48 : $i]: (v1_relat_1 @ (k6_relat_1 @ X48))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.52  thf('31', plain, (![X48 : $i]: (v1_relat_1 @ (k6_relat_1 @ X48))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.21/0.52      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 0.21/0.52  thf(t71_relat_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.21/0.52       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.52  thf('33', plain, (![X42 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X42)) = (X42))),
% 0.21/0.52      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.52  thf('34', plain, (![X48 : $i]: (v1_relat_1 @ (k6_relat_1 @ X48))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.52  thf('35', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ X0)),
% 0.21/0.52      inference('demod', [status(thm)], ['20', '32', '33', '34'])).
% 0.21/0.52  thf('36', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((r1_tarski @ (k3_xboole_0 @ (k2_relat_1 @ (k6_relat_1 @ X1)) @ X0) @ 
% 0.21/0.52           X1)
% 0.21/0.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['5', '35'])).
% 0.21/0.52  thf('37', plain, (![X42 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X42)) = (X42))),
% 0.21/0.52      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.52  thf('38', plain, (![X48 : $i]: (v1_relat_1 @ (k6_relat_1 @ X48))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.52  thf('39', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.21/0.52      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.21/0.52  thf('40', plain, (![X42 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X42)) = (X42))),
% 0.21/0.52      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.52  thf(t125_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ B ) =>
% 0.21/0.52       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.21/0.52         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.21/0.52  thf('41', plain,
% 0.21/0.52      (![X28 : $i, X29 : $i]:
% 0.21/0.52         (~ (r1_tarski @ (k2_relat_1 @ X28) @ X29)
% 0.21/0.52          | ((k8_relat_1 @ X29 @ X28) = (X28))
% 0.21/0.52          | ~ (v1_relat_1 @ X28))),
% 0.21/0.52      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.21/0.52  thf('42', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.52          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.52  thf('43', plain, (![X48 : $i]: (v1_relat_1 @ (k6_relat_1 @ X48))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.52  thf('44', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.52          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 0.21/0.52      inference('demod', [status(thm)], ['42', '43'])).
% 0.21/0.52  thf('45', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 0.21/0.52           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['39', '44'])).
% 0.21/0.52  thf('46', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.21/0.52           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.21/0.52      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.21/0.52  thf(t192_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ B ) =>
% 0.21/0.52       ( ( k7_relat_1 @ B @ A ) =
% 0.21/0.52         ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 0.21/0.52  thf('47', plain,
% 0.21/0.53      (![X33 : $i, X34 : $i]:
% 0.21/0.53         (((k7_relat_1 @ X33 @ X34)
% 0.21/0.53            = (k7_relat_1 @ X33 @ (k3_xboole_0 @ (k1_relat_1 @ X33) @ X34)))
% 0.21/0.53          | ~ (v1_relat_1 @ X33))),
% 0.21/0.53      inference('cnf', [status(esa)], [t192_relat_1])).
% 0.21/0.53  thf('48', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.21/0.53            = (k8_relat_1 @ X1 @ 
% 0.21/0.53               (k6_relat_1 @ 
% 0.21/0.53                (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ X0))))
% 0.21/0.53          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['46', '47'])).
% 0.21/0.53  thf('49', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.21/0.53           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.21/0.53      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.21/0.53  thf('50', plain, (![X41 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X41)) = (X41))),
% 0.21/0.53      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.53  thf('51', plain, (![X48 : $i]: (v1_relat_1 @ (k6_relat_1 @ X48))),
% 0.21/0.53      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.53  thf('52', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.21/0.53           = (k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.21/0.53      inference('demod', [status(thm)], ['48', '49', '50', '51'])).
% 0.21/0.53  thf('53', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.21/0.53           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['45', '52'])).
% 0.21/0.53  thf('54', plain,
% 0.21/0.53      (((k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B))
% 0.21/0.53         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.53      inference('demod', [status(thm)], ['4', '53'])).
% 0.21/0.53  thf('55', plain, ($false), inference('simplify', [status(thm)], ['54'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
