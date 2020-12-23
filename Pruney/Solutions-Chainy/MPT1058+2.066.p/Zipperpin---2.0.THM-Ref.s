%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QC2OtyyoFM

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:46 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 617 expanded)
%              Number of leaves         :   26 ( 228 expanded)
%              Depth                    :   15
%              Number of atoms          :  710 (5142 expanded)
%              Number of equality atoms :   57 ( 488 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t175_funct_2,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
         => ( ( k10_relat_1 @ A @ C )
            = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i,C: $i] :
            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
           => ( ( k10_relat_1 @ A @ C )
              = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t175_funct_2])).

thf('0',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X39 ) @ ( k6_relat_1 @ X38 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X38 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('2',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k7_relat_1 @ X26 @ X25 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X25 ) @ X26 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X19 @ X20 ) )
        = ( k9_relat_1 @ X19 @ X20 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('8',plain,(
    ! [X24: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('9',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(t148_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('11',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k9_relat_1 @ X34 @ ( k10_relat_1 @ X34 @ X33 ) )
        = ( k3_xboole_0 @ X33 @ ( k9_relat_1 @ X34 @ ( k1_relat_1 @ X34 ) ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('14',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('15',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('16',plain,(
    ! [X27: $i] :
      ( ( ( k7_relat_1 @ X27 @ ( k1_relat_1 @ X27 ) )
        = X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('27',plain,(
    ! [X29: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13','14','25','26','27'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('29',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t163_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('32',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( r1_tarski @ X35 @ ( k1_relat_1 @ X36 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X36 @ X35 ) @ X37 )
      | ( r1_tarski @ X35 @ ( k10_relat_1 @ X36 @ X37 ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( r1_tarski @ X1 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('35',plain,(
    ! [X29: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ X1 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['33','34','35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('40',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X31 @ X30 ) @ X32 )
        = ( k3_xboole_0 @ X30 @ ( k10_relat_1 @ X31 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X2 )
        = ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X2 )
      = ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13','14','25','26','27'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['37','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','47'])).

thf('49',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['0','48'])).

thf('50',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('51',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k3_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k3_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13','14','25','26','27'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) )
    = ( k3_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sup+',[status(thm)],['54','57'])).

thf('59',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) )
    = ( k10_relat_1 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['53','58'])).

thf('60',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X31 @ X30 ) @ X32 )
        = ( k3_xboole_0 @ X30 @ ( k10_relat_1 @ X31 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('61',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( k10_relat_1 @ sk_A @ sk_C )
     != ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['59','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QC2OtyyoFM
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:52:57 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.35  % Running portfolio for 600 s
% 0.21/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.21/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.41/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.60  % Solved by: fo/fo7.sh
% 0.41/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.60  % done 256 iterations in 0.154s
% 0.41/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.60  % SZS output start Refutation
% 0.41/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.41/0.60  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.41/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.41/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.60  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.41/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.60  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.41/0.60  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.41/0.60  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.41/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.41/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.41/0.60  thf(t175_funct_2, conjecture,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.41/0.60       ( ![B:$i,C:$i]:
% 0.41/0.60         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.41/0.60           ( ( k10_relat_1 @ A @ C ) =
% 0.41/0.60             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.41/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.60    (~( ![A:$i]:
% 0.41/0.60        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.41/0.60          ( ![B:$i,C:$i]:
% 0.41/0.60            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.41/0.60              ( ( k10_relat_1 @ A @ C ) =
% 0.41/0.60                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.41/0.60    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.41/0.60  thf('0', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(t43_funct_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.41/0.60       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.41/0.60  thf('1', plain,
% 0.41/0.60      (![X38 : $i, X39 : $i]:
% 0.41/0.60         ((k5_relat_1 @ (k6_relat_1 @ X39) @ (k6_relat_1 @ X38))
% 0.41/0.60           = (k6_relat_1 @ (k3_xboole_0 @ X38 @ X39)))),
% 0.41/0.60      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.41/0.60  thf(t94_relat_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( v1_relat_1 @ B ) =>
% 0.41/0.60       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.41/0.60  thf('2', plain,
% 0.41/0.60      (![X25 : $i, X26 : $i]:
% 0.41/0.60         (((k7_relat_1 @ X26 @ X25) = (k5_relat_1 @ (k6_relat_1 @ X25) @ X26))
% 0.41/0.60          | ~ (v1_relat_1 @ X26))),
% 0.41/0.60      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.41/0.60  thf('3', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.41/0.60            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.41/0.60          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.41/0.60      inference('sup+', [status(thm)], ['1', '2'])).
% 0.41/0.60  thf(fc3_funct_1, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.41/0.60       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.41/0.60  thf('4', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 0.41/0.60      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.41/0.60  thf('5', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.41/0.60           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.41/0.60      inference('demod', [status(thm)], ['3', '4'])).
% 0.41/0.60  thf(t148_relat_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( v1_relat_1 @ B ) =>
% 0.41/0.60       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.41/0.60  thf('6', plain,
% 0.41/0.60      (![X19 : $i, X20 : $i]:
% 0.41/0.60         (((k2_relat_1 @ (k7_relat_1 @ X19 @ X20)) = (k9_relat_1 @ X19 @ X20))
% 0.41/0.60          | ~ (v1_relat_1 @ X19))),
% 0.41/0.60      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.41/0.60  thf('7', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         (((k2_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.41/0.60            = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.41/0.60          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.41/0.60      inference('sup+', [status(thm)], ['5', '6'])).
% 0.41/0.60  thf(t71_relat_1, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.41/0.60       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.41/0.60  thf('8', plain, (![X24 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 0.41/0.60      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.41/0.60  thf('9', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 0.41/0.60      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.41/0.60  thf('10', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((k3_xboole_0 @ X1 @ X0) = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.41/0.60      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.41/0.60  thf(t148_funct_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.41/0.60       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 0.41/0.60         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 0.41/0.60  thf('11', plain,
% 0.41/0.60      (![X33 : $i, X34 : $i]:
% 0.41/0.60         (((k9_relat_1 @ X34 @ (k10_relat_1 @ X34 @ X33))
% 0.41/0.60            = (k3_xboole_0 @ X33 @ (k9_relat_1 @ X34 @ (k1_relat_1 @ X34))))
% 0.41/0.60          | ~ (v1_funct_1 @ X34)
% 0.41/0.60          | ~ (v1_relat_1 @ X34))),
% 0.41/0.60      inference('cnf', [status(esa)], [t148_funct_1])).
% 0.41/0.60  thf('12', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         (((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.41/0.60            (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.41/0.60            = (k3_xboole_0 @ X1 @ 
% 0.41/0.60               (k3_xboole_0 @ X0 @ (k1_relat_1 @ (k6_relat_1 @ X0)))))
% 0.41/0.60          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.41/0.60          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 0.41/0.60      inference('sup+', [status(thm)], ['10', '11'])).
% 0.41/0.60  thf('13', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((k3_xboole_0 @ X1 @ X0) = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.41/0.60      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.41/0.60  thf('14', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 0.41/0.60      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.41/0.60  thf('15', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 0.41/0.60      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.41/0.60  thf(t98_relat_1, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( v1_relat_1 @ A ) =>
% 0.41/0.60       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.41/0.60  thf('16', plain,
% 0.41/0.60      (![X27 : $i]:
% 0.41/0.60         (((k7_relat_1 @ X27 @ (k1_relat_1 @ X27)) = (X27))
% 0.41/0.60          | ~ (v1_relat_1 @ X27))),
% 0.41/0.60      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.41/0.60  thf('17', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))
% 0.41/0.60          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.41/0.60      inference('sup+', [status(thm)], ['15', '16'])).
% 0.41/0.60  thf('18', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 0.41/0.60      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.41/0.60  thf('19', plain,
% 0.41/0.60      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.41/0.60      inference('demod', [status(thm)], ['17', '18'])).
% 0.41/0.60  thf('20', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.41/0.60           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.41/0.60      inference('demod', [status(thm)], ['3', '4'])).
% 0.41/0.60  thf('21', plain,
% 0.41/0.60      (![X0 : $i]: ((k6_relat_1 @ (k3_xboole_0 @ X0 @ X0)) = (k6_relat_1 @ X0))),
% 0.41/0.60      inference('demod', [status(thm)], ['19', '20'])).
% 0.41/0.60  thf('22', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 0.41/0.60      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.41/0.60  thf('23', plain,
% 0.41/0.60      (![X0 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 0.41/0.60      inference('sup+', [status(thm)], ['21', '22'])).
% 0.41/0.60  thf('24', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 0.41/0.60      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.41/0.60  thf('25', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.41/0.60      inference('demod', [status(thm)], ['23', '24'])).
% 0.41/0.60  thf('26', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 0.41/0.60      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.41/0.60  thf('27', plain, (![X29 : $i]: (v1_funct_1 @ (k6_relat_1 @ X29))),
% 0.41/0.60      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.41/0.60  thf('28', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((k3_xboole_0 @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.41/0.60           = (k3_xboole_0 @ X1 @ X0))),
% 0.41/0.60      inference('demod', [status(thm)], ['12', '13', '14', '25', '26', '27'])).
% 0.41/0.60  thf(t17_xboole_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.41/0.60  thf('29', plain,
% 0.41/0.60      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 0.41/0.60      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.41/0.60  thf('30', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.41/0.60      inference('sup+', [status(thm)], ['28', '29'])).
% 0.41/0.60  thf('31', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 0.41/0.60      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.41/0.60  thf(t163_funct_1, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.41/0.60       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 0.41/0.60           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 0.41/0.60         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.41/0.60  thf('32', plain,
% 0.41/0.60      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.41/0.60         (~ (r1_tarski @ X35 @ (k1_relat_1 @ X36))
% 0.41/0.60          | ~ (r1_tarski @ (k9_relat_1 @ X36 @ X35) @ X37)
% 0.41/0.60          | (r1_tarski @ X35 @ (k10_relat_1 @ X36 @ X37))
% 0.41/0.60          | ~ (v1_funct_1 @ X36)
% 0.41/0.60          | ~ (v1_relat_1 @ X36))),
% 0.41/0.60      inference('cnf', [status(esa)], [t163_funct_1])).
% 0.41/0.60  thf('33', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.60         (~ (r1_tarski @ X1 @ X0)
% 0.41/0.60          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.41/0.60          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.41/0.60          | (r1_tarski @ X1 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X2))
% 0.41/0.60          | ~ (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X2))),
% 0.41/0.60      inference('sup-', [status(thm)], ['31', '32'])).
% 0.41/0.60  thf('34', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 0.41/0.60      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.41/0.60  thf('35', plain, (![X29 : $i]: (v1_funct_1 @ (k6_relat_1 @ X29))),
% 0.41/0.60      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.41/0.60  thf('36', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((k3_xboole_0 @ X1 @ X0) = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.41/0.60      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.41/0.60  thf('37', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.60         (~ (r1_tarski @ X1 @ X0)
% 0.41/0.60          | (r1_tarski @ X1 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X2))
% 0.41/0.60          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X2))),
% 0.41/0.60      inference('demod', [status(thm)], ['33', '34', '35', '36'])).
% 0.41/0.60  thf('38', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.41/0.60      inference('demod', [status(thm)], ['23', '24'])).
% 0.41/0.60  thf('39', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.41/0.60           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.41/0.60      inference('demod', [status(thm)], ['3', '4'])).
% 0.41/0.60  thf(t139_funct_1, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( v1_relat_1 @ C ) =>
% 0.41/0.60       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.41/0.60         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.41/0.60  thf('40', plain,
% 0.41/0.60      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.41/0.60         (((k10_relat_1 @ (k7_relat_1 @ X31 @ X30) @ X32)
% 0.41/0.60            = (k3_xboole_0 @ X30 @ (k10_relat_1 @ X31 @ X32)))
% 0.41/0.60          | ~ (v1_relat_1 @ X31))),
% 0.41/0.60      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.41/0.60  thf('41', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.60         (((k10_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X2)
% 0.41/0.60            = (k3_xboole_0 @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X1) @ X2)))
% 0.41/0.60          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.41/0.60      inference('sup+', [status(thm)], ['39', '40'])).
% 0.41/0.60  thf('42', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 0.41/0.60      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.41/0.60  thf('43', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.60         ((k10_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X2)
% 0.41/0.60           = (k3_xboole_0 @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X1) @ X2)))),
% 0.41/0.60      inference('demod', [status(thm)], ['41', '42'])).
% 0.41/0.60  thf('44', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((k10_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.41/0.60           = (k3_xboole_0 @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 0.41/0.60      inference('sup+', [status(thm)], ['38', '43'])).
% 0.41/0.60  thf('45', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((k3_xboole_0 @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.41/0.60           = (k3_xboole_0 @ X1 @ X0))),
% 0.41/0.60      inference('demod', [status(thm)], ['12', '13', '14', '25', '26', '27'])).
% 0.41/0.60  thf('46', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((k10_relat_1 @ (k6_relat_1 @ X1) @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.41/0.60      inference('sup+', [status(thm)], ['44', '45'])).
% 0.41/0.60  thf('47', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.60         (~ (r1_tarski @ X1 @ X0)
% 0.41/0.60          | (r1_tarski @ X1 @ (k3_xboole_0 @ X2 @ X0))
% 0.41/0.60          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X2))),
% 0.41/0.60      inference('demod', [status(thm)], ['37', '46'])).
% 0.41/0.60  thf('48', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1)) | ~ (r1_tarski @ X0 @ X1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['30', '47'])).
% 0.41/0.60  thf('49', plain,
% 0.41/0.60      ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ 
% 0.41/0.60        (k3_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B))),
% 0.41/0.60      inference('sup-', [status(thm)], ['0', '48'])).
% 0.41/0.60  thf('50', plain,
% 0.41/0.60      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 0.41/0.60      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.41/0.60  thf(d10_xboole_0, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.41/0.60  thf('51', plain,
% 0.41/0.60      (![X0 : $i, X2 : $i]:
% 0.41/0.60         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.41/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.41/0.60  thf('52', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.41/0.60          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['50', '51'])).
% 0.41/0.60  thf('53', plain,
% 0.41/0.60      (((k10_relat_1 @ sk_A @ sk_C)
% 0.41/0.60         = (k3_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B))),
% 0.41/0.60      inference('sup-', [status(thm)], ['49', '52'])).
% 0.41/0.60  thf('54', plain,
% 0.41/0.60      (((k10_relat_1 @ sk_A @ sk_C)
% 0.41/0.60         = (k3_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B))),
% 0.41/0.60      inference('sup-', [status(thm)], ['49', '52'])).
% 0.41/0.60  thf('55', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((k3_xboole_0 @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.41/0.60           = (k3_xboole_0 @ X1 @ X0))),
% 0.41/0.60      inference('demod', [status(thm)], ['12', '13', '14', '25', '26', '27'])).
% 0.41/0.60  thf('56', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((k10_relat_1 @ (k6_relat_1 @ X1) @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.41/0.60      inference('sup+', [status(thm)], ['44', '45'])).
% 0.41/0.60  thf('57', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.41/0.60           = (k3_xboole_0 @ X1 @ X0))),
% 0.41/0.60      inference('demod', [status(thm)], ['55', '56'])).
% 0.41/0.60  thf('58', plain,
% 0.41/0.60      (((k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C))
% 0.41/0.60         = (k3_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B))),
% 0.41/0.60      inference('sup+', [status(thm)], ['54', '57'])).
% 0.41/0.60  thf('59', plain,
% 0.41/0.60      (((k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C))
% 0.41/0.60         = (k10_relat_1 @ sk_A @ sk_C))),
% 0.41/0.60      inference('sup+', [status(thm)], ['53', '58'])).
% 0.41/0.60  thf('60', plain,
% 0.41/0.60      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.41/0.60         (((k10_relat_1 @ (k7_relat_1 @ X31 @ X30) @ X32)
% 0.41/0.60            = (k3_xboole_0 @ X30 @ (k10_relat_1 @ X31 @ X32)))
% 0.41/0.60          | ~ (v1_relat_1 @ X31))),
% 0.41/0.60      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.41/0.60  thf('61', plain,
% 0.41/0.60      (((k10_relat_1 @ sk_A @ sk_C)
% 0.41/0.60         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('62', plain,
% 0.41/0.60      ((((k10_relat_1 @ sk_A @ sk_C)
% 0.41/0.60          != (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.41/0.60        | ~ (v1_relat_1 @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['60', '61'])).
% 0.41/0.60  thf('63', plain, ((v1_relat_1 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('64', plain,
% 0.41/0.60      (((k10_relat_1 @ sk_A @ sk_C)
% 0.41/0.60         != (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.41/0.60      inference('demod', [status(thm)], ['62', '63'])).
% 0.41/0.60  thf('65', plain, ($false),
% 0.41/0.60      inference('simplify_reflect-', [status(thm)], ['59', '64'])).
% 0.41/0.60  
% 0.41/0.60  % SZS output end Refutation
% 0.41/0.60  
% 0.41/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
