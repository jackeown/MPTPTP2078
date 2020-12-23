%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nWAsehiZbf

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:00 EST 2020

% Result     : Theorem 8.74s
% Output     : Refutation 8.74s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 453 expanded)
%              Number of leaves         :   24 ( 160 expanded)
%              Depth                    :   12
%              Number of atoms          :  874 (3943 expanded)
%              Number of equality atoms :   67 ( 315 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k7_relat_1 @ X26 @ X25 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X25 ) @ X26 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

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
    ( ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
     != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('4',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('5',plain,(
    ! [X18: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('8',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X21 ) @ X22 )
      | ( ( k5_relat_1 @ X21 @ ( k6_relat_1 @ X22 ) )
        = X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','9'])).

thf('11',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k7_relat_1 @ X26 @ X25 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X25 ) @ X26 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
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

thf('14',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) @ X16 )
        = ( k5_relat_1 @ X15 @ ( k5_relat_1 @ X14 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k7_relat_1 @ X26 @ X25 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X25 ) @ X26 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','20'])).

thf('22',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('23',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('24',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('30',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','25','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('34',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('35',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X19 ) @ X20 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X20 ) @ X19 )
        = X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,(
    ! [X18: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t96_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ A @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('40',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k7_relat_1 @ X27 @ X28 )
        = ( k3_xboole_0 @ X27 @ ( k2_zfmisc_1 @ X28 @ ( k2_relat_1 @ X27 ) ) ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t96_relat_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k3_xboole_0 @ ( k6_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ ( k6_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('44',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('49',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','25','31'])).

thf('51',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('52',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X23 @ X24 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X23 ) @ X24 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('57',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X18: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('60',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X21 ) @ X22 )
      | ( ( k5_relat_1 @ X21 @ ( k6_relat_1 @ X22 ) )
        = X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['58','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','25','31'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','25','31'])).

thf('68',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k7_relat_1 @ X26 @ X25 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X25 ) @ X26 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('69',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','25','31'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['38','47','48','49','50','55','66','67','74','75'])).

thf('77',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['4','76'])).

thf('78',plain,(
    $false ),
    inference(simplify,[status(thm)],['77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nWAsehiZbf
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:38:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 8.74/8.97  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 8.74/8.97  % Solved by: fo/fo7.sh
% 8.74/8.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.74/8.97  % done 4716 iterations in 8.512s
% 8.74/8.97  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 8.74/8.97  % SZS output start Refutation
% 8.74/8.97  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.74/8.97  thf(sk_A_type, type, sk_A: $i).
% 8.74/8.97  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 8.74/8.97  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 8.74/8.97  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 8.74/8.97  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 8.74/8.97  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 8.74/8.97  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 8.74/8.97  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 8.74/8.97  thf(sk_B_type, type, sk_B: $i).
% 8.74/8.97  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 8.74/8.97  thf(t94_relat_1, axiom,
% 8.74/8.97    (![A:$i,B:$i]:
% 8.74/8.97     ( ( v1_relat_1 @ B ) =>
% 8.74/8.97       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 8.74/8.97  thf('0', plain,
% 8.74/8.97      (![X25 : $i, X26 : $i]:
% 8.74/8.97         (((k7_relat_1 @ X26 @ X25) = (k5_relat_1 @ (k6_relat_1 @ X25) @ X26))
% 8.74/8.97          | ~ (v1_relat_1 @ X26))),
% 8.74/8.97      inference('cnf', [status(esa)], [t94_relat_1])).
% 8.74/8.97  thf(t43_funct_1, conjecture,
% 8.74/8.97    (![A:$i,B:$i]:
% 8.74/8.97     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 8.74/8.97       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 8.74/8.97  thf(zf_stmt_0, negated_conjecture,
% 8.74/8.97    (~( ![A:$i,B:$i]:
% 8.74/8.97        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 8.74/8.97          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 8.74/8.97    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 8.74/8.97  thf('1', plain,
% 8.74/8.97      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 8.74/8.97         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 8.74/8.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.74/8.97  thf('2', plain,
% 8.74/8.97      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 8.74/8.97          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 8.74/8.97        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 8.74/8.97      inference('sup-', [status(thm)], ['0', '1'])).
% 8.74/8.97  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 8.74/8.97  thf('3', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 8.74/8.97      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 8.74/8.97  thf('4', plain,
% 8.74/8.97      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 8.74/8.97         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 8.74/8.97      inference('demod', [status(thm)], ['2', '3'])).
% 8.74/8.97  thf(t71_relat_1, axiom,
% 8.74/8.97    (![A:$i]:
% 8.74/8.97     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 8.74/8.97       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 8.74/8.97  thf('5', plain, (![X18 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X18)) = (X18))),
% 8.74/8.97      inference('cnf', [status(esa)], [t71_relat_1])).
% 8.74/8.97  thf(d10_xboole_0, axiom,
% 8.74/8.97    (![A:$i,B:$i]:
% 8.74/8.97     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 8.74/8.97  thf('6', plain,
% 8.74/8.97      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 8.74/8.97      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.74/8.97  thf('7', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 8.74/8.97      inference('simplify', [status(thm)], ['6'])).
% 8.74/8.97  thf(t79_relat_1, axiom,
% 8.74/8.97    (![A:$i,B:$i]:
% 8.74/8.97     ( ( v1_relat_1 @ B ) =>
% 8.74/8.97       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 8.74/8.97         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 8.74/8.97  thf('8', plain,
% 8.74/8.97      (![X21 : $i, X22 : $i]:
% 8.74/8.97         (~ (r1_tarski @ (k2_relat_1 @ X21) @ X22)
% 8.74/8.97          | ((k5_relat_1 @ X21 @ (k6_relat_1 @ X22)) = (X21))
% 8.74/8.97          | ~ (v1_relat_1 @ X21))),
% 8.74/8.97      inference('cnf', [status(esa)], [t79_relat_1])).
% 8.74/8.97  thf('9', plain,
% 8.74/8.97      (![X0 : $i]:
% 8.74/8.97         (~ (v1_relat_1 @ X0)
% 8.74/8.97          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0))) = (X0)))),
% 8.74/8.97      inference('sup-', [status(thm)], ['7', '8'])).
% 8.74/8.97  thf('10', plain,
% 8.74/8.97      (![X0 : $i]:
% 8.74/8.97         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 8.74/8.97            = (k6_relat_1 @ X0))
% 8.74/8.97          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 8.74/8.97      inference('sup+', [status(thm)], ['5', '9'])).
% 8.74/8.97  thf('11', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 8.74/8.97      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 8.74/8.97  thf('12', plain,
% 8.74/8.97      (![X0 : $i]:
% 8.74/8.97         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 8.74/8.97           = (k6_relat_1 @ X0))),
% 8.74/8.97      inference('demod', [status(thm)], ['10', '11'])).
% 8.74/8.97  thf('13', plain,
% 8.74/8.97      (![X25 : $i, X26 : $i]:
% 8.74/8.97         (((k7_relat_1 @ X26 @ X25) = (k5_relat_1 @ (k6_relat_1 @ X25) @ X26))
% 8.74/8.97          | ~ (v1_relat_1 @ X26))),
% 8.74/8.97      inference('cnf', [status(esa)], [t94_relat_1])).
% 8.74/8.97  thf(t55_relat_1, axiom,
% 8.74/8.97    (![A:$i]:
% 8.74/8.97     ( ( v1_relat_1 @ A ) =>
% 8.74/8.97       ( ![B:$i]:
% 8.74/8.97         ( ( v1_relat_1 @ B ) =>
% 8.74/8.97           ( ![C:$i]:
% 8.74/8.97             ( ( v1_relat_1 @ C ) =>
% 8.74/8.97               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 8.74/8.97                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 8.74/8.97  thf('14', plain,
% 8.74/8.97      (![X14 : $i, X15 : $i, X16 : $i]:
% 8.74/8.97         (~ (v1_relat_1 @ X14)
% 8.74/8.97          | ((k5_relat_1 @ (k5_relat_1 @ X15 @ X14) @ X16)
% 8.74/8.97              = (k5_relat_1 @ X15 @ (k5_relat_1 @ X14 @ X16)))
% 8.74/8.97          | ~ (v1_relat_1 @ X16)
% 8.74/8.97          | ~ (v1_relat_1 @ X15))),
% 8.74/8.97      inference('cnf', [status(esa)], [t55_relat_1])).
% 8.74/8.97  thf('15', plain,
% 8.74/8.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.74/8.97         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 8.74/8.97            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 8.74/8.97          | ~ (v1_relat_1 @ X1)
% 8.74/8.97          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 8.74/8.97          | ~ (v1_relat_1 @ X2)
% 8.74/8.97          | ~ (v1_relat_1 @ X1))),
% 8.74/8.97      inference('sup+', [status(thm)], ['13', '14'])).
% 8.74/8.97  thf('16', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 8.74/8.97      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 8.74/8.97  thf('17', plain,
% 8.74/8.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.74/8.97         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 8.74/8.97            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 8.74/8.97          | ~ (v1_relat_1 @ X1)
% 8.74/8.97          | ~ (v1_relat_1 @ X2)
% 8.74/8.97          | ~ (v1_relat_1 @ X1))),
% 8.74/8.97      inference('demod', [status(thm)], ['15', '16'])).
% 8.74/8.97  thf('18', plain,
% 8.74/8.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.74/8.97         (~ (v1_relat_1 @ X2)
% 8.74/8.97          | ~ (v1_relat_1 @ X1)
% 8.74/8.97          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 8.74/8.97              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 8.74/8.97      inference('simplify', [status(thm)], ['17'])).
% 8.74/8.97  thf('19', plain,
% 8.74/8.97      (![X25 : $i, X26 : $i]:
% 8.74/8.97         (((k7_relat_1 @ X26 @ X25) = (k5_relat_1 @ (k6_relat_1 @ X25) @ X26))
% 8.74/8.97          | ~ (v1_relat_1 @ X26))),
% 8.74/8.97      inference('cnf', [status(esa)], [t94_relat_1])).
% 8.74/8.97  thf('20', plain,
% 8.74/8.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.74/8.97         (((k7_relat_1 @ (k5_relat_1 @ X2 @ X0) @ X1)
% 8.74/8.97            = (k5_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 8.74/8.97          | ~ (v1_relat_1 @ X2)
% 8.74/8.97          | ~ (v1_relat_1 @ X0)
% 8.74/8.97          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X0)))),
% 8.74/8.97      inference('sup+', [status(thm)], ['18', '19'])).
% 8.74/8.97  thf('21', plain,
% 8.74/8.97      (![X0 : $i, X1 : $i]:
% 8.74/8.97         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 8.74/8.97          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 8.74/8.97          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 8.74/8.97          | ((k7_relat_1 @ 
% 8.74/8.97              (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0)) @ X1)
% 8.74/8.97              = (k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 8.74/8.97                 (k6_relat_1 @ X0))))),
% 8.74/8.97      inference('sup-', [status(thm)], ['12', '20'])).
% 8.74/8.97  thf('22', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 8.74/8.97      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 8.74/8.97  thf('23', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 8.74/8.97      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 8.74/8.97  thf('24', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 8.74/8.97      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 8.74/8.97  thf('25', plain,
% 8.74/8.97      (![X0 : $i]:
% 8.74/8.97         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 8.74/8.97           = (k6_relat_1 @ X0))),
% 8.74/8.97      inference('demod', [status(thm)], ['10', '11'])).
% 8.74/8.97  thf('26', plain,
% 8.74/8.97      (![X0 : $i]:
% 8.74/8.97         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 8.74/8.97           = (k6_relat_1 @ X0))),
% 8.74/8.97      inference('demod', [status(thm)], ['10', '11'])).
% 8.74/8.97  thf('27', plain,
% 8.74/8.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.74/8.97         (~ (v1_relat_1 @ X2)
% 8.74/8.97          | ~ (v1_relat_1 @ X1)
% 8.74/8.97          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 8.74/8.97              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 8.74/8.97      inference('simplify', [status(thm)], ['17'])).
% 8.74/8.97  thf('28', plain,
% 8.74/8.97      (![X0 : $i, X1 : $i]:
% 8.74/8.97         (((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 8.74/8.97            (k6_relat_1 @ X0))
% 8.74/8.97            = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 8.74/8.97          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 8.74/8.97          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 8.74/8.97      inference('sup+', [status(thm)], ['26', '27'])).
% 8.74/8.97  thf('29', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 8.74/8.97      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 8.74/8.97  thf('30', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 8.74/8.97      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 8.74/8.97  thf('31', plain,
% 8.74/8.97      (![X0 : $i, X1 : $i]:
% 8.74/8.97         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ 
% 8.74/8.97           (k6_relat_1 @ X0))
% 8.74/8.97           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 8.74/8.97      inference('demod', [status(thm)], ['28', '29', '30'])).
% 8.74/8.97  thf('32', plain,
% 8.74/8.97      (![X0 : $i, X1 : $i]:
% 8.74/8.97         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 8.74/8.97           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 8.74/8.97      inference('demod', [status(thm)], ['21', '22', '23', '24', '25', '31'])).
% 8.74/8.97  thf('33', plain,
% 8.74/8.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.74/8.97         (~ (v1_relat_1 @ X2)
% 8.74/8.97          | ~ (v1_relat_1 @ X1)
% 8.74/8.97          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 8.74/8.97              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 8.74/8.97      inference('simplify', [status(thm)], ['17'])).
% 8.74/8.97  thf('34', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 8.74/8.97      inference('simplify', [status(thm)], ['6'])).
% 8.74/8.97  thf(t77_relat_1, axiom,
% 8.74/8.97    (![A:$i,B:$i]:
% 8.74/8.97     ( ( v1_relat_1 @ B ) =>
% 8.74/8.97       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 8.74/8.97         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 8.74/8.97  thf('35', plain,
% 8.74/8.97      (![X19 : $i, X20 : $i]:
% 8.74/8.97         (~ (r1_tarski @ (k1_relat_1 @ X19) @ X20)
% 8.74/8.97          | ((k5_relat_1 @ (k6_relat_1 @ X20) @ X19) = (X19))
% 8.74/8.97          | ~ (v1_relat_1 @ X19))),
% 8.74/8.97      inference('cnf', [status(esa)], [t77_relat_1])).
% 8.74/8.97  thf('36', plain,
% 8.74/8.97      (![X0 : $i]:
% 8.74/8.97         (~ (v1_relat_1 @ X0)
% 8.74/8.97          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 8.74/8.97      inference('sup-', [status(thm)], ['34', '35'])).
% 8.74/8.97  thf('37', plain,
% 8.74/8.97      (![X0 : $i, X1 : $i]:
% 8.74/8.97         (((k5_relat_1 @ 
% 8.74/8.97            (k7_relat_1 @ X1 @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))) @ X0)
% 8.74/8.97            = (k5_relat_1 @ X1 @ X0))
% 8.74/8.97          | ~ (v1_relat_1 @ X1)
% 8.74/8.97          | ~ (v1_relat_1 @ X0)
% 8.74/8.97          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 8.74/8.97      inference('sup+', [status(thm)], ['33', '36'])).
% 8.74/8.97  thf('38', plain,
% 8.74/8.97      (![X0 : $i, X1 : $i]:
% 8.74/8.97         (~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 8.74/8.97          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 8.74/8.97          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 8.74/8.97          | ((k5_relat_1 @ 
% 8.74/8.97              (k7_relat_1 @ (k6_relat_1 @ X0) @ 
% 8.74/8.97               (k1_relat_1 @ 
% 8.74/8.97                (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))) @ 
% 8.74/8.97              (k6_relat_1 @ X1))
% 8.74/8.97              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))))),
% 8.74/8.97      inference('sup-', [status(thm)], ['32', '37'])).
% 8.74/8.97  thf('39', plain, (![X18 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X18)) = (X18))),
% 8.74/8.97      inference('cnf', [status(esa)], [t71_relat_1])).
% 8.74/8.97  thf(t96_relat_1, axiom,
% 8.74/8.97    (![A:$i,B:$i]:
% 8.74/8.97     ( ( v1_relat_1 @ B ) =>
% 8.74/8.97       ( ( k7_relat_1 @ B @ A ) =
% 8.74/8.97         ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ A @ ( k2_relat_1 @ B ) ) ) ) ))).
% 8.74/8.97  thf('40', plain,
% 8.74/8.97      (![X27 : $i, X28 : $i]:
% 8.74/8.97         (((k7_relat_1 @ X27 @ X28)
% 8.74/8.97            = (k3_xboole_0 @ X27 @ (k2_zfmisc_1 @ X28 @ (k2_relat_1 @ X27))))
% 8.74/8.97          | ~ (v1_relat_1 @ X27))),
% 8.74/8.97      inference('cnf', [status(esa)], [t96_relat_1])).
% 8.74/8.97  thf('41', plain,
% 8.74/8.97      (![X0 : $i, X1 : $i]:
% 8.74/8.97         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 8.74/8.97            = (k3_xboole_0 @ (k6_relat_1 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))
% 8.74/8.97          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 8.74/8.97      inference('sup+', [status(thm)], ['39', '40'])).
% 8.74/8.97  thf('42', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 8.74/8.97      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 8.74/8.97  thf('43', plain,
% 8.74/8.97      (![X0 : $i, X1 : $i]:
% 8.74/8.97         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 8.74/8.97           = (k3_xboole_0 @ (k6_relat_1 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 8.74/8.97      inference('demod', [status(thm)], ['41', '42'])).
% 8.74/8.97  thf(fc1_relat_1, axiom,
% 8.74/8.97    (![A:$i,B:$i]:
% 8.74/8.97     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 8.74/8.97  thf('44', plain,
% 8.74/8.97      (![X12 : $i, X13 : $i]:
% 8.74/8.97         (~ (v1_relat_1 @ X12) | (v1_relat_1 @ (k3_xboole_0 @ X12 @ X13)))),
% 8.74/8.97      inference('cnf', [status(esa)], [fc1_relat_1])).
% 8.74/8.97  thf('45', plain,
% 8.74/8.97      (![X0 : $i, X1 : $i]:
% 8.74/8.97         ((v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 8.74/8.97          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 8.74/8.97      inference('sup+', [status(thm)], ['43', '44'])).
% 8.74/8.97  thf('46', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 8.74/8.97      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 8.74/8.97  thf('47', plain,
% 8.74/8.97      (![X0 : $i, X1 : $i]:
% 8.74/8.97         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 8.74/8.97      inference('demod', [status(thm)], ['45', '46'])).
% 8.74/8.97  thf('48', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 8.74/8.97      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 8.74/8.97  thf('49', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 8.74/8.97      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 8.74/8.97  thf('50', plain,
% 8.74/8.97      (![X0 : $i, X1 : $i]:
% 8.74/8.97         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 8.74/8.97           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 8.74/8.97      inference('demod', [status(thm)], ['21', '22', '23', '24', '25', '31'])).
% 8.74/8.97  thf('51', plain, (![X17 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X17)) = (X17))),
% 8.74/8.97      inference('cnf', [status(esa)], [t71_relat_1])).
% 8.74/8.97  thf(t90_relat_1, axiom,
% 8.74/8.97    (![A:$i,B:$i]:
% 8.74/8.97     ( ( v1_relat_1 @ B ) =>
% 8.74/8.97       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 8.74/8.97         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 8.74/8.97  thf('52', plain,
% 8.74/8.97      (![X23 : $i, X24 : $i]:
% 8.74/8.97         (((k1_relat_1 @ (k7_relat_1 @ X23 @ X24))
% 8.74/8.97            = (k3_xboole_0 @ (k1_relat_1 @ X23) @ X24))
% 8.74/8.97          | ~ (v1_relat_1 @ X23))),
% 8.74/8.97      inference('cnf', [status(esa)], [t90_relat_1])).
% 8.74/8.97  thf('53', plain,
% 8.74/8.97      (![X0 : $i, X1 : $i]:
% 8.74/8.97         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 8.74/8.97            = (k3_xboole_0 @ X0 @ X1))
% 8.74/8.97          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 8.74/8.97      inference('sup+', [status(thm)], ['51', '52'])).
% 8.74/8.97  thf('54', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 8.74/8.97      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 8.74/8.97  thf('55', plain,
% 8.74/8.97      (![X0 : $i, X1 : $i]:
% 8.74/8.97         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 8.74/8.97           = (k3_xboole_0 @ X0 @ X1))),
% 8.74/8.97      inference('demod', [status(thm)], ['53', '54'])).
% 8.74/8.97  thf(commutativity_k3_xboole_0, axiom,
% 8.74/8.97    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 8.74/8.97  thf('56', plain,
% 8.74/8.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 8.74/8.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 8.74/8.97  thf(t17_xboole_1, axiom,
% 8.74/8.97    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 8.74/8.97  thf('57', plain,
% 8.74/8.97      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 8.74/8.97      inference('cnf', [status(esa)], [t17_xboole_1])).
% 8.74/8.97  thf('58', plain,
% 8.74/8.97      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 8.74/8.97      inference('sup+', [status(thm)], ['56', '57'])).
% 8.74/8.97  thf('59', plain, (![X18 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X18)) = (X18))),
% 8.74/8.97      inference('cnf', [status(esa)], [t71_relat_1])).
% 8.74/8.97  thf('60', plain,
% 8.74/8.97      (![X21 : $i, X22 : $i]:
% 8.74/8.97         (~ (r1_tarski @ (k2_relat_1 @ X21) @ X22)
% 8.74/8.97          | ((k5_relat_1 @ X21 @ (k6_relat_1 @ X22)) = (X21))
% 8.74/8.97          | ~ (v1_relat_1 @ X21))),
% 8.74/8.97      inference('cnf', [status(esa)], [t79_relat_1])).
% 8.74/8.97  thf('61', plain,
% 8.74/8.97      (![X0 : $i, X1 : $i]:
% 8.74/8.97         (~ (r1_tarski @ X0 @ X1)
% 8.74/8.97          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 8.74/8.97          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 8.74/8.97              = (k6_relat_1 @ X0)))),
% 8.74/8.97      inference('sup-', [status(thm)], ['59', '60'])).
% 8.74/8.97  thf('62', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 8.74/8.97      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 8.74/8.97  thf('63', plain,
% 8.74/8.97      (![X0 : $i, X1 : $i]:
% 8.74/8.97         (~ (r1_tarski @ X0 @ X1)
% 8.74/8.97          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 8.74/8.97              = (k6_relat_1 @ X0)))),
% 8.74/8.97      inference('demod', [status(thm)], ['61', '62'])).
% 8.74/8.97  thf('64', plain,
% 8.74/8.97      (![X0 : $i, X1 : $i]:
% 8.74/8.97         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 8.74/8.97           (k6_relat_1 @ X0)) = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 8.74/8.97      inference('sup-', [status(thm)], ['58', '63'])).
% 8.74/8.97  thf('65', plain,
% 8.74/8.97      (![X0 : $i, X1 : $i]:
% 8.74/8.97         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 8.74/8.97           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 8.74/8.97      inference('demod', [status(thm)], ['21', '22', '23', '24', '25', '31'])).
% 8.74/8.97  thf('66', plain,
% 8.74/8.97      (![X0 : $i, X1 : $i]:
% 8.74/8.97         ((k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 8.74/8.97           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 8.74/8.97      inference('demod', [status(thm)], ['64', '65'])).
% 8.74/8.97  thf('67', plain,
% 8.74/8.97      (![X0 : $i, X1 : $i]:
% 8.74/8.97         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 8.74/8.97           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 8.74/8.97      inference('demod', [status(thm)], ['21', '22', '23', '24', '25', '31'])).
% 8.74/8.97  thf('68', plain,
% 8.74/8.97      (![X25 : $i, X26 : $i]:
% 8.74/8.97         (((k7_relat_1 @ X26 @ X25) = (k5_relat_1 @ (k6_relat_1 @ X25) @ X26))
% 8.74/8.97          | ~ (v1_relat_1 @ X26))),
% 8.74/8.97      inference('cnf', [status(esa)], [t94_relat_1])).
% 8.74/8.97  thf('69', plain,
% 8.74/8.97      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 8.74/8.97      inference('cnf', [status(esa)], [t17_xboole_1])).
% 8.74/8.97  thf('70', plain,
% 8.74/8.97      (![X0 : $i, X1 : $i]:
% 8.74/8.97         (~ (r1_tarski @ X0 @ X1)
% 8.74/8.97          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 8.74/8.97              = (k6_relat_1 @ X0)))),
% 8.74/8.97      inference('demod', [status(thm)], ['61', '62'])).
% 8.74/8.97  thf('71', plain,
% 8.74/8.97      (![X0 : $i, X1 : $i]:
% 8.74/8.97         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 8.74/8.97           (k6_relat_1 @ X0)) = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 8.74/8.97      inference('sup-', [status(thm)], ['69', '70'])).
% 8.74/8.97  thf('72', plain,
% 8.74/8.97      (![X0 : $i, X1 : $i]:
% 8.74/8.97         (((k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 8.74/8.97            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 8.74/8.97          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 8.74/8.97      inference('sup+', [status(thm)], ['68', '71'])).
% 8.74/8.97  thf('73', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 8.74/8.97      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 8.74/8.97  thf('74', plain,
% 8.74/8.97      (![X0 : $i, X1 : $i]:
% 8.74/8.97         ((k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 8.74/8.97           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 8.74/8.97      inference('demod', [status(thm)], ['72', '73'])).
% 8.74/8.97  thf('75', plain,
% 8.74/8.97      (![X0 : $i, X1 : $i]:
% 8.74/8.97         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 8.74/8.97           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 8.74/8.97      inference('demod', [status(thm)], ['21', '22', '23', '24', '25', '31'])).
% 8.74/8.97  thf('76', plain,
% 8.74/8.97      (![X0 : $i, X1 : $i]:
% 8.74/8.97         ((k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 8.74/8.97           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 8.74/8.97      inference('demod', [status(thm)],
% 8.74/8.97                ['38', '47', '48', '49', '50', '55', '66', '67', '74', '75'])).
% 8.74/8.97  thf('77', plain,
% 8.74/8.97      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 8.74/8.97         != (k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 8.74/8.97      inference('demod', [status(thm)], ['4', '76'])).
% 8.74/8.97  thf('78', plain, ($false), inference('simplify', [status(thm)], ['77'])).
% 8.74/8.97  
% 8.74/8.97  % SZS output end Refutation
% 8.74/8.97  
% 8.74/8.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
