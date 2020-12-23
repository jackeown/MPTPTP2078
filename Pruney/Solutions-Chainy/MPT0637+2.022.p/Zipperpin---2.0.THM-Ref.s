%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SGnJ7Q4egY

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:58 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  171 (1265 expanded)
%              Number of leaves         :   33 ( 475 expanded)
%              Depth                    :   17
%              Number of atoms          : 1417 (10060 expanded)
%              Number of equality atoms :  120 ( 870 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k8_relat_1 @ X24 @ X23 )
        = ( k5_relat_1 @ X23 @ ( k6_relat_1 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
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

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('4',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k8_relat_1 @ X24 @ X23 )
        = ( k5_relat_1 @ X23 @ ( k6_relat_1 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('6',plain,(
    ! [X44: $i,X45: $i] :
      ( ( ( k7_relat_1 @ X45 @ X44 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X44 ) @ X45 ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('7',plain,(
    ! [X37: $i,X38: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X37 @ ( k6_relat_1 @ X38 ) ) @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v1_relat_1 @ X30 )
      | ( r1_tarski @ ( k1_relat_1 @ X31 ) @ ( k1_relat_1 @ X30 ) )
      | ~ ( r1_tarski @ X31 @ X30 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('12',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k8_relat_1 @ X24 @ X23 )
        = ( k5_relat_1 @ X23 @ ( k6_relat_1 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('13',plain,(
    ! [X44: $i,X45: $i] :
      ( ( ( k7_relat_1 @ X45 @ X44 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X44 ) @ X45 ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('16',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('18',plain,(
    ! [X34: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X34 ) )
      = X34 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t124_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('19',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k8_relat_1 @ X26 @ X25 )
        = ( k3_xboole_0 @ X25 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X25 ) @ X26 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t124_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k3_xboole_0 @ ( k6_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k3_xboole_0 @ ( k6_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('23',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('28',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('29',plain,(
    ! [X34: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X34 ) )
      = X34 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) @ X0 ) ),
    inference(demod,[status(thm)],['11','17','26','27','28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('33',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X42 @ X43 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X42 ) @ X43 ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X34: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X34 ) )
      = X34 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('36',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['31','37','38'])).

thf('40',plain,(
    ! [X34: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X34 ) )
      = X34 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('41',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X39 ) @ X40 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X40 ) @ X39 )
        = X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k8_relat_1 @ X24 @ X23 )
        = ( k5_relat_1 @ X23 @ ( k6_relat_1 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t72_relat_1,axiom,(
    ! [A: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('47',plain,(
    ! [X36: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X36 ) )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('48',plain,(
    ! [X36: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X36 ) )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('49',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v1_relat_1 @ X32 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X33 @ X32 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X32 ) @ ( k4_relat_1 @ X33 ) ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','52'])).

thf('54',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','55'])).

thf('57',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('60',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('64',plain,(
    ! [X41: $i] :
      ( ( ( k5_relat_1 @ X41 @ ( k6_relat_1 @ ( k2_relat_1 @ X41 ) ) )
        = X41 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('65',plain,(
    ! [X44: $i,X45: $i] :
      ( ( ( k7_relat_1 @ X45 @ X44 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X44 ) @ X45 ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X35: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X35 ) )
      = X35 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('68',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('69',plain,(
    ! [X35: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X35 ) )
      = X35 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('70',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['66','67','68','69','70'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('72',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) @ X19 )
        = ( k7_relat_1 @ X17 @ ( k3_xboole_0 @ X18 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['63','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','58','79'])).

thf(involutiveness_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) )
        = A ) ) )).

thf('81',plain,(
    ! [X16: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X16 ) )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X36: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X36 ) )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k8_relat_1 @ sk_B @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['63','78'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k8_relat_1 @ X24 @ X23 )
        = ( k5_relat_1 @ X23 @ ( k6_relat_1 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('95',plain,(
    ! [X35: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X35 ) )
      = X35 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('96',plain,(
    ! [X41: $i] :
      ( ( ( k5_relat_1 @ X41 @ ( k6_relat_1 @ ( k2_relat_1 @ X41 ) ) )
        = X41 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['94','99'])).

thf('101',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['93','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','58','79'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X36: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X36 ) )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X1 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('117',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) @ X19 )
        = ( k7_relat_1 @ X17 @ ( k3_xboole_0 @ X18 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('118',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X42 @ X43 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X42 ) @ X43 ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['116','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('122',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('127',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['120','121','122','123','124','125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['115','127','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['107','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['105','106','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['131','132','133'])).

thf('135',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['86','134'])).

thf('136',plain,(
    $false ),
    inference(simplify,[status(thm)],['135'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SGnJ7Q4egY
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:21:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.58/0.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.77  % Solved by: fo/fo7.sh
% 0.58/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.77  % done 608 iterations in 0.332s
% 0.58/0.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.77  % SZS output start Refutation
% 0.58/0.77  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.58/0.77  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.58/0.77  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.58/0.77  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.58/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.77  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.58/0.77  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.58/0.77  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.58/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.77  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.58/0.77  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.58/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.77  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.58/0.77  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.58/0.77  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.58/0.77  thf(t123_relat_1, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( v1_relat_1 @ B ) =>
% 0.58/0.77       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.58/0.77  thf('0', plain,
% 0.58/0.77      (![X23 : $i, X24 : $i]:
% 0.58/0.77         (((k8_relat_1 @ X24 @ X23) = (k5_relat_1 @ X23 @ (k6_relat_1 @ X24)))
% 0.58/0.77          | ~ (v1_relat_1 @ X23))),
% 0.58/0.77      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.58/0.77  thf(t43_funct_1, conjecture,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.58/0.77       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.58/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.77    (~( ![A:$i,B:$i]:
% 0.58/0.77        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.58/0.77          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.58/0.77    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 0.58/0.77  thf('1', plain,
% 0.58/0.77      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.58/0.77         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('2', plain,
% 0.58/0.77      ((((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.58/0.77          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 0.58/0.77        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['0', '1'])).
% 0.58/0.77  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.58/0.77  thf('3', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.58/0.77      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.58/0.77  thf('4', plain,
% 0.58/0.77      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.58/0.77         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.58/0.77      inference('demod', [status(thm)], ['2', '3'])).
% 0.58/0.77  thf('5', plain,
% 0.58/0.77      (![X23 : $i, X24 : $i]:
% 0.58/0.77         (((k8_relat_1 @ X24 @ X23) = (k5_relat_1 @ X23 @ (k6_relat_1 @ X24)))
% 0.58/0.77          | ~ (v1_relat_1 @ X23))),
% 0.58/0.77      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.58/0.77  thf(t94_relat_1, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( v1_relat_1 @ B ) =>
% 0.58/0.77       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.58/0.77  thf('6', plain,
% 0.58/0.77      (![X44 : $i, X45 : $i]:
% 0.58/0.77         (((k7_relat_1 @ X45 @ X44) = (k5_relat_1 @ (k6_relat_1 @ X44) @ X45))
% 0.58/0.77          | ~ (v1_relat_1 @ X45))),
% 0.58/0.77      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.58/0.77  thf(t76_relat_1, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( v1_relat_1 @ B ) =>
% 0.58/0.77       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 0.58/0.77         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 0.58/0.77  thf('7', plain,
% 0.58/0.77      (![X37 : $i, X38 : $i]:
% 0.58/0.77         ((r1_tarski @ (k5_relat_1 @ X37 @ (k6_relat_1 @ X38)) @ X37)
% 0.58/0.77          | ~ (v1_relat_1 @ X37))),
% 0.58/0.77      inference('cnf', [status(esa)], [t76_relat_1])).
% 0.58/0.77  thf(t25_relat_1, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( v1_relat_1 @ A ) =>
% 0.58/0.77       ( ![B:$i]:
% 0.58/0.77         ( ( v1_relat_1 @ B ) =>
% 0.58/0.77           ( ( r1_tarski @ A @ B ) =>
% 0.58/0.77             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.58/0.77               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.58/0.77  thf('8', plain,
% 0.58/0.77      (![X30 : $i, X31 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ X30)
% 0.58/0.77          | (r1_tarski @ (k1_relat_1 @ X31) @ (k1_relat_1 @ X30))
% 0.58/0.77          | ~ (r1_tarski @ X31 @ X30)
% 0.58/0.77          | ~ (v1_relat_1 @ X31))),
% 0.58/0.77      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.58/0.77  thf('9', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ X0)
% 0.58/0.77          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.58/0.77          | (r1_tarski @ 
% 0.58/0.77             (k1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))) @ 
% 0.58/0.77             (k1_relat_1 @ X0))
% 0.58/0.77          | ~ (v1_relat_1 @ X0))),
% 0.58/0.77      inference('sup-', [status(thm)], ['7', '8'])).
% 0.58/0.77  thf('10', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))) @ 
% 0.58/0.77           (k1_relat_1 @ X0))
% 0.58/0.77          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.58/0.77          | ~ (v1_relat_1 @ X0))),
% 0.58/0.77      inference('simplify', [status(thm)], ['9'])).
% 0.58/0.77  thf('11', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.58/0.77          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.58/0.77          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.58/0.77          | (r1_tarski @ 
% 0.58/0.77             (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))) @ 
% 0.58/0.77             (k1_relat_1 @ (k6_relat_1 @ X0))))),
% 0.58/0.77      inference('sup-', [status(thm)], ['6', '10'])).
% 0.58/0.77  thf('12', plain,
% 0.58/0.77      (![X23 : $i, X24 : $i]:
% 0.58/0.77         (((k8_relat_1 @ X24 @ X23) = (k5_relat_1 @ X23 @ (k6_relat_1 @ X24)))
% 0.58/0.77          | ~ (v1_relat_1 @ X23))),
% 0.58/0.77      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.58/0.77  thf('13', plain,
% 0.58/0.77      (![X44 : $i, X45 : $i]:
% 0.58/0.77         (((k7_relat_1 @ X45 @ X44) = (k5_relat_1 @ (k6_relat_1 @ X44) @ X45))
% 0.58/0.77          | ~ (v1_relat_1 @ X45))),
% 0.58/0.77      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.58/0.77  thf('14', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.58/0.77            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.58/0.77          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.58/0.77          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.58/0.77      inference('sup+', [status(thm)], ['12', '13'])).
% 0.58/0.77  thf('15', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.58/0.77      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.58/0.77  thf('16', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.58/0.77      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.58/0.77  thf('17', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.58/0.77           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.58/0.77      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.58/0.77  thf(t71_relat_1, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.58/0.77       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.58/0.77  thf('18', plain, (![X34 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X34)) = (X34))),
% 0.58/0.77      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.58/0.77  thf(t124_relat_1, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( v1_relat_1 @ B ) =>
% 0.58/0.77       ( ( k8_relat_1 @ A @ B ) =
% 0.58/0.77         ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 0.58/0.77  thf('19', plain,
% 0.58/0.77      (![X25 : $i, X26 : $i]:
% 0.58/0.77         (((k8_relat_1 @ X26 @ X25)
% 0.58/0.77            = (k3_xboole_0 @ X25 @ (k2_zfmisc_1 @ (k1_relat_1 @ X25) @ X26)))
% 0.58/0.77          | ~ (v1_relat_1 @ X25))),
% 0.58/0.77      inference('cnf', [status(esa)], [t124_relat_1])).
% 0.58/0.77  thf('20', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.58/0.77            = (k3_xboole_0 @ (k6_relat_1 @ X0) @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.58/0.77          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.58/0.77      inference('sup+', [status(thm)], ['18', '19'])).
% 0.58/0.77  thf('21', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.58/0.77      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.58/0.77  thf('22', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.58/0.77           = (k3_xboole_0 @ (k6_relat_1 @ X0) @ (k2_zfmisc_1 @ X0 @ X1)))),
% 0.58/0.77      inference('demod', [status(thm)], ['20', '21'])).
% 0.58/0.77  thf(fc1_relat_1, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.58/0.77  thf('23', plain,
% 0.58/0.77      (![X14 : $i, X15 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ X14) | (v1_relat_1 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.58/0.77      inference('cnf', [status(esa)], [fc1_relat_1])).
% 0.58/0.77  thf('24', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.58/0.77          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.58/0.77      inference('sup+', [status(thm)], ['22', '23'])).
% 0.58/0.77  thf('25', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.58/0.77      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.58/0.77  thf('26', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.58/0.77      inference('demod', [status(thm)], ['24', '25'])).
% 0.58/0.77  thf('27', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.58/0.77      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.58/0.77  thf('28', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.58/0.77      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.58/0.77  thf('29', plain, (![X34 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X34)) = (X34))),
% 0.58/0.77      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.58/0.77  thf('30', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (r1_tarski @ 
% 0.58/0.77          (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))) @ 
% 0.58/0.77          X0)),
% 0.58/0.77      inference('demod', [status(thm)], ['11', '17', '26', '27', '28', '29'])).
% 0.58/0.77  thf('31', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((r1_tarski @ (k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.58/0.77           X0)
% 0.58/0.77          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.58/0.77      inference('sup+', [status(thm)], ['5', '30'])).
% 0.58/0.77  thf('32', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.58/0.77           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.58/0.77      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.58/0.77  thf(t90_relat_1, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( v1_relat_1 @ B ) =>
% 0.58/0.77       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.58/0.77         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.58/0.77  thf('33', plain,
% 0.58/0.77      (![X42 : $i, X43 : $i]:
% 0.58/0.77         (((k1_relat_1 @ (k7_relat_1 @ X42 @ X43))
% 0.58/0.77            = (k3_xboole_0 @ (k1_relat_1 @ X42) @ X43))
% 0.58/0.77          | ~ (v1_relat_1 @ X42))),
% 0.58/0.77      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.58/0.77  thf('34', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.58/0.77            = (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ X0))
% 0.58/0.77          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.58/0.77      inference('sup+', [status(thm)], ['32', '33'])).
% 0.58/0.77  thf('35', plain, (![X34 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X34)) = (X34))),
% 0.58/0.77      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.58/0.77  thf('36', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.58/0.77      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.58/0.77  thf('37', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.58/0.77           = (k3_xboole_0 @ X1 @ X0))),
% 0.58/0.77      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.58/0.77  thf('38', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.58/0.77      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.58/0.77  thf('39', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.58/0.77      inference('demod', [status(thm)], ['31', '37', '38'])).
% 0.58/0.77  thf('40', plain, (![X34 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X34)) = (X34))),
% 0.58/0.77      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.58/0.77  thf(t77_relat_1, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( v1_relat_1 @ B ) =>
% 0.58/0.77       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.58/0.77         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 0.58/0.77  thf('41', plain,
% 0.58/0.77      (![X39 : $i, X40 : $i]:
% 0.58/0.77         (~ (r1_tarski @ (k1_relat_1 @ X39) @ X40)
% 0.58/0.77          | ((k5_relat_1 @ (k6_relat_1 @ X40) @ X39) = (X39))
% 0.58/0.77          | ~ (v1_relat_1 @ X39))),
% 0.58/0.77      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.58/0.77  thf('42', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (~ (r1_tarski @ X0 @ X1)
% 0.58/0.77          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.58/0.77          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 0.58/0.77              = (k6_relat_1 @ X0)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['40', '41'])).
% 0.58/0.77  thf('43', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.58/0.77      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.58/0.77  thf('44', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (~ (r1_tarski @ X0 @ X1)
% 0.58/0.77          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 0.58/0.77              = (k6_relat_1 @ X0)))),
% 0.58/0.77      inference('demod', [status(thm)], ['42', '43'])).
% 0.58/0.77  thf('45', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.58/0.77           (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.58/0.77           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['39', '44'])).
% 0.58/0.77  thf('46', plain,
% 0.58/0.77      (![X23 : $i, X24 : $i]:
% 0.58/0.77         (((k8_relat_1 @ X24 @ X23) = (k5_relat_1 @ X23 @ (k6_relat_1 @ X24)))
% 0.58/0.77          | ~ (v1_relat_1 @ X23))),
% 0.58/0.77      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.58/0.77  thf(t72_relat_1, axiom,
% 0.58/0.77    (![A:$i]: ( ( k4_relat_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.58/0.77  thf('47', plain,
% 0.58/0.77      (![X36 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X36)) = (k6_relat_1 @ X36))),
% 0.58/0.77      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.58/0.77  thf('48', plain,
% 0.58/0.77      (![X36 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X36)) = (k6_relat_1 @ X36))),
% 0.58/0.77      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.58/0.77  thf(t54_relat_1, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( v1_relat_1 @ A ) =>
% 0.58/0.77       ( ![B:$i]:
% 0.58/0.77         ( ( v1_relat_1 @ B ) =>
% 0.58/0.77           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.58/0.77             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 0.58/0.77  thf('49', plain,
% 0.58/0.77      (![X32 : $i, X33 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ X32)
% 0.58/0.77          | ((k4_relat_1 @ (k5_relat_1 @ X33 @ X32))
% 0.58/0.77              = (k5_relat_1 @ (k4_relat_1 @ X32) @ (k4_relat_1 @ X33)))
% 0.58/0.77          | ~ (v1_relat_1 @ X33))),
% 0.58/0.77      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.58/0.77  thf('50', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.58/0.77            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.58/0.77          | ~ (v1_relat_1 @ X1)
% 0.58/0.77          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.58/0.77      inference('sup+', [status(thm)], ['48', '49'])).
% 0.58/0.77  thf('51', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.58/0.77      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.58/0.77  thf('52', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.58/0.77            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.58/0.77          | ~ (v1_relat_1 @ X1))),
% 0.58/0.77      inference('demod', [status(thm)], ['50', '51'])).
% 0.58/0.77  thf('53', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))
% 0.58/0.77            = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 0.58/0.77          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.58/0.77      inference('sup+', [status(thm)], ['47', '52'])).
% 0.58/0.77  thf('54', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.58/0.77      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.58/0.77  thf('55', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))
% 0.58/0.77           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.58/0.77      inference('demod', [status(thm)], ['53', '54'])).
% 0.58/0.77  thf('56', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.58/0.77            = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 0.58/0.77          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.58/0.77      inference('sup+', [status(thm)], ['46', '55'])).
% 0.58/0.77  thf('57', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.58/0.77      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.58/0.77  thf('58', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k4_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.58/0.77           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.58/0.77      inference('demod', [status(thm)], ['56', '57'])).
% 0.58/0.77  thf(commutativity_k2_tarski, axiom,
% 0.58/0.77    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.58/0.77  thf('59', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.58/0.77      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.58/0.77  thf(t12_setfam_1, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.58/0.77  thf('60', plain,
% 0.58/0.77      (![X11 : $i, X12 : $i]:
% 0.58/0.77         ((k1_setfam_1 @ (k2_tarski @ X11 @ X12)) = (k3_xboole_0 @ X11 @ X12))),
% 0.58/0.77      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.58/0.77  thf('61', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.58/0.77      inference('sup+', [status(thm)], ['59', '60'])).
% 0.58/0.77  thf('62', plain,
% 0.58/0.77      (![X11 : $i, X12 : $i]:
% 0.58/0.77         ((k1_setfam_1 @ (k2_tarski @ X11 @ X12)) = (k3_xboole_0 @ X11 @ X12))),
% 0.58/0.77      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.58/0.77  thf('63', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.58/0.77      inference('sup+', [status(thm)], ['61', '62'])).
% 0.58/0.77  thf(t80_relat_1, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( v1_relat_1 @ A ) =>
% 0.58/0.77       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.58/0.77  thf('64', plain,
% 0.58/0.77      (![X41 : $i]:
% 0.58/0.77         (((k5_relat_1 @ X41 @ (k6_relat_1 @ (k2_relat_1 @ X41))) = (X41))
% 0.58/0.77          | ~ (v1_relat_1 @ X41))),
% 0.58/0.77      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.58/0.77  thf('65', plain,
% 0.58/0.77      (![X44 : $i, X45 : $i]:
% 0.58/0.77         (((k7_relat_1 @ X45 @ X44) = (k5_relat_1 @ (k6_relat_1 @ X44) @ X45))
% 0.58/0.77          | ~ (v1_relat_1 @ X45))),
% 0.58/0.77      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.58/0.77  thf('66', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (((k7_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0))) @ X0)
% 0.58/0.77            = (k6_relat_1 @ X0))
% 0.58/0.77          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.58/0.77          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0)))))),
% 0.58/0.77      inference('sup+', [status(thm)], ['64', '65'])).
% 0.58/0.77  thf('67', plain, (![X35 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X35)) = (X35))),
% 0.58/0.77      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.58/0.77  thf('68', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.58/0.77      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.58/0.77  thf('69', plain, (![X35 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X35)) = (X35))),
% 0.58/0.77      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.58/0.77  thf('70', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.58/0.77      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.58/0.77  thf('71', plain,
% 0.58/0.77      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.58/0.77      inference('demod', [status(thm)], ['66', '67', '68', '69', '70'])).
% 0.58/0.77  thf(t100_relat_1, axiom,
% 0.58/0.77    (![A:$i,B:$i,C:$i]:
% 0.58/0.77     ( ( v1_relat_1 @ C ) =>
% 0.58/0.77       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.58/0.77         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.58/0.77  thf('72', plain,
% 0.58/0.77      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.58/0.77         (((k7_relat_1 @ (k7_relat_1 @ X17 @ X18) @ X19)
% 0.58/0.77            = (k7_relat_1 @ X17 @ (k3_xboole_0 @ X18 @ X19)))
% 0.58/0.77          | ~ (v1_relat_1 @ X17))),
% 0.58/0.77      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.58/0.77  thf('73', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.58/0.77            = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))
% 0.58/0.77          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.58/0.77      inference('sup+', [status(thm)], ['71', '72'])).
% 0.58/0.77  thf('74', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.58/0.77      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.58/0.77  thf('75', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.58/0.77           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.58/0.77      inference('demod', [status(thm)], ['73', '74'])).
% 0.58/0.77  thf('76', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.58/0.77           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.58/0.77      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.58/0.77  thf('77', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.58/0.77           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.58/0.77      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.58/0.77  thf('78', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.58/0.77           = (k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))))),
% 0.58/0.77      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.58/0.77  thf('79', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.58/0.77           = (k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.58/0.77      inference('sup+', [status(thm)], ['63', '78'])).
% 0.58/0.77  thf('80', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k4_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.58/0.77           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.58/0.77      inference('demod', [status(thm)], ['45', '58', '79'])).
% 0.58/0.77  thf(involutiveness_k4_relat_1, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( v1_relat_1 @ A ) => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) ) = ( A ) ) ))).
% 0.58/0.77  thf('81', plain,
% 0.58/0.77      (![X16 : $i]:
% 0.58/0.77         (((k4_relat_1 @ (k4_relat_1 @ X16)) = (X16)) | ~ (v1_relat_1 @ X16))),
% 0.58/0.77      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 0.58/0.77  thf('82', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (((k4_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.58/0.77            = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.58/0.77          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 0.58/0.77      inference('sup+', [status(thm)], ['80', '81'])).
% 0.58/0.77  thf('83', plain,
% 0.58/0.77      (![X36 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X36)) = (k6_relat_1 @ X36))),
% 0.58/0.77      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.58/0.77  thf('84', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.58/0.77      inference('demod', [status(thm)], ['24', '25'])).
% 0.58/0.77  thf('85', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 0.58/0.77           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 0.58/0.77      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.58/0.77  thf('86', plain,
% 0.58/0.77      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.58/0.77         != (k8_relat_1 @ sk_B @ (k6_relat_1 @ sk_A)))),
% 0.58/0.77      inference('demod', [status(thm)], ['4', '85'])).
% 0.58/0.77  thf('87', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.58/0.77           = (k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))))),
% 0.58/0.77      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.58/0.77  thf('88', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.58/0.77           = (k3_xboole_0 @ X1 @ X0))),
% 0.58/0.77      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.58/0.77  thf('89', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.58/0.77           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.58/0.77      inference('sup+', [status(thm)], ['87', '88'])).
% 0.58/0.77  thf('90', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.58/0.77           = (k3_xboole_0 @ X1 @ X0))),
% 0.58/0.77      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.58/0.77  thf('91', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k3_xboole_0 @ X1 @ X0)
% 0.58/0.77           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.58/0.77      inference('demod', [status(thm)], ['89', '90'])).
% 0.58/0.77  thf('92', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.58/0.77           = (k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.58/0.77      inference('sup+', [status(thm)], ['63', '78'])).
% 0.58/0.77  thf('93', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ (k6_relat_1 @ X1))
% 0.58/0.77           = (k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.58/0.77              (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.58/0.77      inference('sup+', [status(thm)], ['91', '92'])).
% 0.58/0.77  thf('94', plain,
% 0.58/0.77      (![X23 : $i, X24 : $i]:
% 0.58/0.77         (((k8_relat_1 @ X24 @ X23) = (k5_relat_1 @ X23 @ (k6_relat_1 @ X24)))
% 0.58/0.77          | ~ (v1_relat_1 @ X23))),
% 0.58/0.77      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.58/0.77  thf('95', plain, (![X35 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X35)) = (X35))),
% 0.58/0.77      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.58/0.77  thf('96', plain,
% 0.58/0.77      (![X41 : $i]:
% 0.58/0.77         (((k5_relat_1 @ X41 @ (k6_relat_1 @ (k2_relat_1 @ X41))) = (X41))
% 0.58/0.77          | ~ (v1_relat_1 @ X41))),
% 0.58/0.77      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.58/0.77  thf('97', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.58/0.77            = (k6_relat_1 @ X0))
% 0.58/0.77          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.58/0.77      inference('sup+', [status(thm)], ['95', '96'])).
% 0.58/0.77  thf('98', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.58/0.77      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.58/0.77  thf('99', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.58/0.77           = (k6_relat_1 @ X0))),
% 0.58/0.77      inference('demod', [status(thm)], ['97', '98'])).
% 0.58/0.77  thf('100', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))
% 0.58/0.77          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.58/0.77      inference('sup+', [status(thm)], ['94', '99'])).
% 0.58/0.77  thf('101', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.58/0.77      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.58/0.77  thf('102', plain,
% 0.58/0.77      (![X0 : $i]: ((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 0.58/0.77      inference('demod', [status(thm)], ['100', '101'])).
% 0.58/0.77  thf('103', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k8_relat_1 @ (k3_xboole_0 @ X1 @ X0) @ (k6_relat_1 @ X1))
% 0.58/0.77           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.58/0.77      inference('demod', [status(thm)], ['93', '102'])).
% 0.58/0.77  thf('104', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k4_relat_1 @ (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.58/0.77           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.58/0.77      inference('demod', [status(thm)], ['45', '58', '79'])).
% 0.58/0.77  thf('105', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k4_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.58/0.77           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.58/0.77      inference('sup+', [status(thm)], ['103', '104'])).
% 0.58/0.77  thf('106', plain,
% 0.58/0.77      (![X36 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X36)) = (k6_relat_1 @ X36))),
% 0.58/0.77      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.58/0.77  thf('107', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.58/0.77      inference('sup+', [status(thm)], ['61', '62'])).
% 0.58/0.77  thf('108', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.58/0.77      inference('sup+', [status(thm)], ['61', '62'])).
% 0.58/0.77  thf('109', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k3_xboole_0 @ X1 @ X0)
% 0.58/0.77           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.58/0.77      inference('demod', [status(thm)], ['89', '90'])).
% 0.58/0.77  thf('110', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k3_xboole_0 @ X0 @ X1)
% 0.58/0.77           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.58/0.77      inference('sup+', [status(thm)], ['108', '109'])).
% 0.58/0.77  thf('111', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k3_xboole_0 @ X0 @ X1)
% 0.58/0.77           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.58/0.77      inference('sup+', [status(thm)], ['108', '109'])).
% 0.58/0.77  thf('112', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X1)
% 0.58/0.77           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.58/0.77      inference('sup+', [status(thm)], ['110', '111'])).
% 0.58/0.77  thf('113', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.58/0.77      inference('sup+', [status(thm)], ['61', '62'])).
% 0.58/0.77  thf('114', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k3_xboole_0 @ X0 @ X1)
% 0.58/0.77           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.58/0.77      inference('sup+', [status(thm)], ['108', '109'])).
% 0.58/0.77  thf('115', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k3_xboole_0 @ X1 @ X0)
% 0.58/0.77           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.58/0.77      inference('demod', [status(thm)], ['112', '113', '114'])).
% 0.58/0.77  thf('116', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.58/0.77           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.58/0.77      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.58/0.77  thf('117', plain,
% 0.58/0.77      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.58/0.77         (((k7_relat_1 @ (k7_relat_1 @ X17 @ X18) @ X19)
% 0.58/0.77            = (k7_relat_1 @ X17 @ (k3_xboole_0 @ X18 @ X19)))
% 0.58/0.77          | ~ (v1_relat_1 @ X17))),
% 0.58/0.77      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.58/0.77  thf('118', plain,
% 0.58/0.77      (![X42 : $i, X43 : $i]:
% 0.58/0.77         (((k1_relat_1 @ (k7_relat_1 @ X42 @ X43))
% 0.58/0.77            = (k3_xboole_0 @ (k1_relat_1 @ X42) @ X43))
% 0.58/0.77          | ~ (v1_relat_1 @ X42))),
% 0.58/0.77      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.58/0.77  thf('119', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.77         (((k1_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.58/0.77            = (k3_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X2 @ X1)) @ X0))
% 0.58/0.77          | ~ (v1_relat_1 @ X2)
% 0.58/0.77          | ~ (v1_relat_1 @ (k7_relat_1 @ X2 @ X1)))),
% 0.58/0.77      inference('sup+', [status(thm)], ['117', '118'])).
% 0.58/0.77  thf('120', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.58/0.77          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.58/0.77          | ((k1_relat_1 @ 
% 0.58/0.77              (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X0 @ X2)))
% 0.58/0.77              = (k3_xboole_0 @ 
% 0.58/0.77                 (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ X2)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['116', '119'])).
% 0.58/0.77  thf('121', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (v1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.58/0.77      inference('demod', [status(thm)], ['24', '25'])).
% 0.58/0.77  thf('122', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.58/0.77      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.58/0.77  thf('123', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.58/0.77           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.58/0.77      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.58/0.77  thf('124', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.58/0.77           = (k3_xboole_0 @ X1 @ X0))),
% 0.58/0.77      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.58/0.77  thf('125', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.58/0.77           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.58/0.77      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.58/0.77  thf('126', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.58/0.77           = (k3_xboole_0 @ X1 @ X0))),
% 0.58/0.77      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.58/0.77  thf('127', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.77         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X2))
% 0.58/0.77           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 0.58/0.77      inference('demod', [status(thm)],
% 0.58/0.77                ['120', '121', '122', '123', '124', '125', '126'])).
% 0.58/0.77  thf('128', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k3_xboole_0 @ X1 @ X0)
% 0.58/0.77           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.58/0.77      inference('demod', [status(thm)], ['89', '90'])).
% 0.58/0.77  thf('129', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k3_xboole_0 @ X1 @ X0)
% 0.58/0.77           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.58/0.77      inference('demod', [status(thm)], ['115', '127', '128'])).
% 0.58/0.77  thf('130', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k3_xboole_0 @ X0 @ X1)
% 0.58/0.77           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.58/0.77      inference('sup+', [status(thm)], ['107', '129'])).
% 0.58/0.77  thf('131', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 0.58/0.77           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.58/0.77      inference('demod', [status(thm)], ['105', '106', '130'])).
% 0.58/0.77  thf('132', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 0.58/0.77           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 0.58/0.77      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.58/0.77  thf('133', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 0.58/0.77           = (k8_relat_1 @ X0 @ (k6_relat_1 @ X1)))),
% 0.58/0.77      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.58/0.77  thf('134', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.58/0.77           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.58/0.77      inference('demod', [status(thm)], ['131', '132', '133'])).
% 0.58/0.77  thf('135', plain,
% 0.58/0.77      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.58/0.77         != (k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B)))),
% 0.58/0.77      inference('demod', [status(thm)], ['86', '134'])).
% 0.58/0.77  thf('136', plain, ($false), inference('simplify', [status(thm)], ['135'])).
% 0.58/0.77  
% 0.58/0.77  % SZS output end Refutation
% 0.58/0.77  
% 0.58/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
