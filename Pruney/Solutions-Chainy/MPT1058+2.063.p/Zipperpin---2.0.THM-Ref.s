%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XSFEJOEZ9u

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:46 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 323 expanded)
%              Number of leaves         :   26 ( 122 expanded)
%              Depth                    :   17
%              Number of atoms          :  701 (2677 expanded)
%              Number of equality atoms :   61 ( 242 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('0',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X27 @ X26 ) @ X28 )
        = ( k3_xboole_0 @ X26 @ ( k10_relat_1 @ X27 @ X28 ) ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

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

thf('1',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('2',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('3',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ X29 @ ( k2_relat_1 @ X30 ) )
      | ( ( k9_relat_1 @ X30 @ ( k10_relat_1 @ X30 @ X29 ) )
        = X29 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('6',plain,(
    ! [X25: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X15 @ X16 ) )
        = ( k9_relat_1 @ X15 @ X16 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X37 ) @ ( k6_relat_1 @ X36 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('9',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k7_relat_1 @ X23 @ X22 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X22 ) @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['7','14'])).

thf('16',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['4','5','6','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t148_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('20',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k9_relat_1 @ X32 @ ( k10_relat_1 @ X32 @ X31 ) )
        = ( k3_xboole_0 @ X31 @ ( k9_relat_1 @ X32 @ ( k1_relat_1 @ X32 ) ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('23',plain,(
    ! [X20: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('24',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('25',plain,(
    ! [X25: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X0 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['18','26'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X0 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['18','26'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('33',plain,(
    ! [X19: $i] :
      ( ( ( k10_relat_1 @ X19 @ ( k2_relat_1 @ X19 ) )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X20: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('36',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','25'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference(demod,[status(thm)],['27','40'])).

thf('42',plain,
    ( ( k3_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B )
    = ( k10_relat_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('44',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X27 @ X26 ) @ X28 )
        = ( k3_xboole_0 @ X26 @ ( k10_relat_1 @ X27 @ X28 ) ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('48',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X17 @ X18 ) @ ( k1_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('51',plain,(
    ! [X20: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('54',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['49','52','55'])).

thf('57',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['49','52','55'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) )
    = ( k10_relat_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['42','60'])).

thf('62',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C )
      = ( k10_relat_1 @ sk_A @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C )
    = ( k10_relat_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XSFEJOEZ9u
% 0.15/0.38  % Computer   : n024.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 18:40:51 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.39  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 0.60/0.84  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.60/0.84  % Solved by: fo/fo7.sh
% 0.60/0.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.84  % done 533 iterations in 0.344s
% 0.60/0.84  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.60/0.84  % SZS output start Refutation
% 0.60/0.84  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.60/0.84  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.60/0.84  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.60/0.84  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.60/0.84  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.84  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.60/0.84  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.60/0.84  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.60/0.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.60/0.84  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.60/0.84  thf(sk_C_type, type, sk_C: $i).
% 0.60/0.84  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.60/0.84  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.60/0.84  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.84  thf(t139_funct_1, axiom,
% 0.60/0.84    (![A:$i,B:$i,C:$i]:
% 0.60/0.84     ( ( v1_relat_1 @ C ) =>
% 0.60/0.84       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.60/0.84         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.60/0.84  thf('0', plain,
% 0.60/0.84      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.60/0.84         (((k10_relat_1 @ (k7_relat_1 @ X27 @ X26) @ X28)
% 0.60/0.84            = (k3_xboole_0 @ X26 @ (k10_relat_1 @ X27 @ X28)))
% 0.60/0.84          | ~ (v1_relat_1 @ X27))),
% 0.60/0.84      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.60/0.84  thf(t175_funct_2, conjecture,
% 0.60/0.84    (![A:$i]:
% 0.60/0.84     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.60/0.84       ( ![B:$i,C:$i]:
% 0.60/0.84         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.60/0.84           ( ( k10_relat_1 @ A @ C ) =
% 0.60/0.84             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.60/0.84  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.84    (~( ![A:$i]:
% 0.60/0.84        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.60/0.84          ( ![B:$i,C:$i]:
% 0.60/0.84            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.60/0.84              ( ( k10_relat_1 @ A @ C ) =
% 0.60/0.84                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.60/0.84    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.60/0.84  thf('1', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf(t71_relat_1, axiom,
% 0.60/0.84    (![A:$i]:
% 0.60/0.84     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.60/0.84       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.60/0.84  thf('2', plain, (![X21 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 0.60/0.84      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.60/0.84  thf(t147_funct_1, axiom,
% 0.60/0.84    (![A:$i,B:$i]:
% 0.60/0.84     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.60/0.84       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.60/0.84         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.60/0.84  thf('3', plain,
% 0.60/0.84      (![X29 : $i, X30 : $i]:
% 0.60/0.84         (~ (r1_tarski @ X29 @ (k2_relat_1 @ X30))
% 0.60/0.84          | ((k9_relat_1 @ X30 @ (k10_relat_1 @ X30 @ X29)) = (X29))
% 0.60/0.84          | ~ (v1_funct_1 @ X30)
% 0.60/0.84          | ~ (v1_relat_1 @ X30))),
% 0.60/0.84      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.60/0.84  thf('4', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         (~ (r1_tarski @ X1 @ X0)
% 0.60/0.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.60/0.84          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.60/0.84          | ((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.60/0.84              (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)) = (X1)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['2', '3'])).
% 0.60/0.84  thf(fc3_funct_1, axiom,
% 0.60/0.84    (![A:$i]:
% 0.60/0.84     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.60/0.84       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.60/0.84  thf('5', plain, (![X24 : $i]: (v1_relat_1 @ (k6_relat_1 @ X24))),
% 0.60/0.84      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.60/0.84  thf('6', plain, (![X25 : $i]: (v1_funct_1 @ (k6_relat_1 @ X25))),
% 0.60/0.84      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.60/0.84  thf(t148_relat_1, axiom,
% 0.60/0.84    (![A:$i,B:$i]:
% 0.60/0.84     ( ( v1_relat_1 @ B ) =>
% 0.60/0.84       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.60/0.84  thf('7', plain,
% 0.60/0.84      (![X15 : $i, X16 : $i]:
% 0.60/0.84         (((k2_relat_1 @ (k7_relat_1 @ X15 @ X16)) = (k9_relat_1 @ X15 @ X16))
% 0.60/0.84          | ~ (v1_relat_1 @ X15))),
% 0.60/0.84      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.60/0.84  thf(t43_funct_1, axiom,
% 0.60/0.84    (![A:$i,B:$i]:
% 0.60/0.84     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.60/0.84       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.60/0.84  thf('8', plain,
% 0.60/0.84      (![X36 : $i, X37 : $i]:
% 0.60/0.84         ((k5_relat_1 @ (k6_relat_1 @ X37) @ (k6_relat_1 @ X36))
% 0.60/0.84           = (k6_relat_1 @ (k3_xboole_0 @ X36 @ X37)))),
% 0.60/0.84      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.60/0.84  thf(t94_relat_1, axiom,
% 0.60/0.84    (![A:$i,B:$i]:
% 0.60/0.84     ( ( v1_relat_1 @ B ) =>
% 0.60/0.84       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.60/0.84  thf('9', plain,
% 0.60/0.84      (![X22 : $i, X23 : $i]:
% 0.60/0.84         (((k7_relat_1 @ X23 @ X22) = (k5_relat_1 @ (k6_relat_1 @ X22) @ X23))
% 0.60/0.84          | ~ (v1_relat_1 @ X23))),
% 0.60/0.84      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.60/0.84  thf('10', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.60/0.84            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.60/0.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.60/0.84      inference('sup+', [status(thm)], ['8', '9'])).
% 0.60/0.84  thf('11', plain, (![X24 : $i]: (v1_relat_1 @ (k6_relat_1 @ X24))),
% 0.60/0.84      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.60/0.84  thf('12', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.60/0.84           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.60/0.84      inference('demod', [status(thm)], ['10', '11'])).
% 0.60/0.84  thf('13', plain, (![X21 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 0.60/0.84      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.60/0.84  thf('14', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         ((k2_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.60/0.84           = (k3_xboole_0 @ X1 @ X0))),
% 0.60/0.84      inference('sup+', [status(thm)], ['12', '13'])).
% 0.60/0.84  thf('15', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         (((k9_relat_1 @ (k6_relat_1 @ X1) @ X0) = (k3_xboole_0 @ X1 @ X0))
% 0.60/0.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.60/0.84      inference('sup+', [status(thm)], ['7', '14'])).
% 0.60/0.84  thf('16', plain, (![X24 : $i]: (v1_relat_1 @ (k6_relat_1 @ X24))),
% 0.60/0.84      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.60/0.84  thf('17', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         ((k9_relat_1 @ (k6_relat_1 @ X1) @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.60/0.84      inference('demod', [status(thm)], ['15', '16'])).
% 0.60/0.84  thf('18', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         (~ (r1_tarski @ X1 @ X0)
% 0.60/0.84          | ((k3_xboole_0 @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)) = (X1)))),
% 0.60/0.84      inference('demod', [status(thm)], ['4', '5', '6', '17'])).
% 0.60/0.84  thf('19', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         ((k9_relat_1 @ (k6_relat_1 @ X1) @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.60/0.84      inference('demod', [status(thm)], ['15', '16'])).
% 0.60/0.84  thf(t148_funct_1, axiom,
% 0.60/0.84    (![A:$i,B:$i]:
% 0.60/0.84     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.60/0.84       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 0.60/0.84         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 0.60/0.84  thf('20', plain,
% 0.60/0.84      (![X31 : $i, X32 : $i]:
% 0.60/0.84         (((k9_relat_1 @ X32 @ (k10_relat_1 @ X32 @ X31))
% 0.60/0.84            = (k3_xboole_0 @ X31 @ (k9_relat_1 @ X32 @ (k1_relat_1 @ X32))))
% 0.60/0.84          | ~ (v1_funct_1 @ X32)
% 0.60/0.84          | ~ (v1_relat_1 @ X32))),
% 0.60/0.84      inference('cnf', [status(esa)], [t148_funct_1])).
% 0.60/0.84  thf('21', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         (((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.60/0.84            (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.60/0.84            = (k3_xboole_0 @ X1 @ 
% 0.60/0.84               (k3_xboole_0 @ X0 @ (k1_relat_1 @ (k6_relat_1 @ X0)))))
% 0.60/0.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.60/0.84          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 0.60/0.84      inference('sup+', [status(thm)], ['19', '20'])).
% 0.60/0.84  thf('22', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         ((k9_relat_1 @ (k6_relat_1 @ X1) @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.60/0.84      inference('demod', [status(thm)], ['15', '16'])).
% 0.60/0.84  thf('23', plain, (![X20 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X20)) = (X20))),
% 0.60/0.84      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.60/0.84  thf('24', plain, (![X24 : $i]: (v1_relat_1 @ (k6_relat_1 @ X24))),
% 0.60/0.84      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.60/0.84  thf('25', plain, (![X25 : $i]: (v1_funct_1 @ (k6_relat_1 @ X25))),
% 0.60/0.84      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.60/0.84  thf('26', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         ((k3_xboole_0 @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.60/0.84           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X0)))),
% 0.60/0.84      inference('demod', [status(thm)], ['21', '22', '23', '24', '25'])).
% 0.60/0.84  thf('27', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         (~ (r1_tarski @ X1 @ X0)
% 0.60/0.84          | ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X0)) = (X1)))),
% 0.60/0.84      inference('demod', [status(thm)], ['18', '26'])).
% 0.60/0.84  thf(d10_xboole_0, axiom,
% 0.60/0.84    (![A:$i,B:$i]:
% 0.60/0.84     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.60/0.84  thf('28', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.60/0.84      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.60/0.84  thf('29', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.60/0.84      inference('simplify', [status(thm)], ['28'])).
% 0.60/0.84  thf('30', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         (~ (r1_tarski @ X1 @ X0)
% 0.60/0.84          | ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X0)) = (X1)))),
% 0.60/0.84      inference('demod', [status(thm)], ['18', '26'])).
% 0.60/0.84  thf('31', plain,
% 0.60/0.84      (![X0 : $i]: ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0)) = (X0))),
% 0.60/0.84      inference('sup-', [status(thm)], ['29', '30'])).
% 0.60/0.84  thf('32', plain, (![X21 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 0.60/0.84      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.60/0.84  thf(t169_relat_1, axiom,
% 0.60/0.84    (![A:$i]:
% 0.60/0.84     ( ( v1_relat_1 @ A ) =>
% 0.60/0.84       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.60/0.84  thf('33', plain,
% 0.60/0.84      (![X19 : $i]:
% 0.60/0.84         (((k10_relat_1 @ X19 @ (k2_relat_1 @ X19)) = (k1_relat_1 @ X19))
% 0.60/0.84          | ~ (v1_relat_1 @ X19))),
% 0.60/0.84      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.60/0.84  thf('34', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         (((k10_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 0.60/0.84            = (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.60/0.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.60/0.84      inference('sup+', [status(thm)], ['32', '33'])).
% 0.60/0.84  thf('35', plain, (![X20 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X20)) = (X20))),
% 0.60/0.84      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.60/0.84  thf('36', plain, (![X24 : $i]: (v1_relat_1 @ (k6_relat_1 @ X24))),
% 0.60/0.84      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.60/0.84  thf('37', plain,
% 0.60/0.84      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.60/0.84      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.60/0.84  thf('38', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         ((k3_xboole_0 @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.60/0.84           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X0)))),
% 0.60/0.84      inference('demod', [status(thm)], ['21', '22', '23', '24', '25'])).
% 0.60/0.84  thf('39', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         ((k3_xboole_0 @ X0 @ X0)
% 0.60/0.84           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0)))),
% 0.60/0.84      inference('sup+', [status(thm)], ['37', '38'])).
% 0.60/0.84  thf('40', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.60/0.84      inference('sup+', [status(thm)], ['31', '39'])).
% 0.60/0.84  thf('41', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         (~ (r1_tarski @ X1 @ X0) | ((k3_xboole_0 @ X1 @ X0) = (X1)))),
% 0.60/0.84      inference('demod', [status(thm)], ['27', '40'])).
% 0.60/0.84  thf('42', plain,
% 0.60/0.84      (((k3_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)
% 0.60/0.84         = (k10_relat_1 @ sk_A @ sk_C))),
% 0.60/0.84      inference('sup-', [status(thm)], ['1', '41'])).
% 0.60/0.84  thf('43', plain,
% 0.60/0.84      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.60/0.84      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.60/0.84  thf('44', plain,
% 0.60/0.84      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.60/0.84         (((k10_relat_1 @ (k7_relat_1 @ X27 @ X26) @ X28)
% 0.60/0.84            = (k3_xboole_0 @ X26 @ (k10_relat_1 @ X27 @ X28)))
% 0.60/0.84          | ~ (v1_relat_1 @ X27))),
% 0.60/0.84      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.60/0.84  thf('45', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         (((k10_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)
% 0.60/0.84            = (k3_xboole_0 @ X1 @ X0))
% 0.60/0.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.60/0.84      inference('sup+', [status(thm)], ['43', '44'])).
% 0.60/0.84  thf('46', plain, (![X24 : $i]: (v1_relat_1 @ (k6_relat_1 @ X24))),
% 0.60/0.84      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.60/0.84  thf('47', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         ((k10_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)
% 0.60/0.84           = (k3_xboole_0 @ X1 @ X0))),
% 0.60/0.84      inference('demod', [status(thm)], ['45', '46'])).
% 0.60/0.84  thf(t167_relat_1, axiom,
% 0.60/0.84    (![A:$i,B:$i]:
% 0.60/0.84     ( ( v1_relat_1 @ B ) =>
% 0.60/0.84       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.60/0.84  thf('48', plain,
% 0.60/0.84      (![X17 : $i, X18 : $i]:
% 0.60/0.84         ((r1_tarski @ (k10_relat_1 @ X17 @ X18) @ (k1_relat_1 @ X17))
% 0.60/0.84          | ~ (v1_relat_1 @ X17))),
% 0.60/0.84      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.60/0.84  thf('49', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.60/0.84           (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.60/0.84          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 0.60/0.84      inference('sup+', [status(thm)], ['47', '48'])).
% 0.60/0.84  thf('50', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.60/0.84           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.60/0.84      inference('demod', [status(thm)], ['10', '11'])).
% 0.60/0.84  thf('51', plain, (![X20 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X20)) = (X20))),
% 0.60/0.84      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.60/0.84  thf('52', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.60/0.84           = (k3_xboole_0 @ X1 @ X0))),
% 0.60/0.84      inference('sup+', [status(thm)], ['50', '51'])).
% 0.60/0.84  thf('53', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.60/0.84           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.60/0.84      inference('demod', [status(thm)], ['10', '11'])).
% 0.60/0.84  thf('54', plain, (![X24 : $i]: (v1_relat_1 @ (k6_relat_1 @ X24))),
% 0.60/0.84      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.60/0.84  thf('55', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.60/0.84      inference('sup+', [status(thm)], ['53', '54'])).
% 0.60/0.84  thf('56', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1))),
% 0.60/0.84      inference('demod', [status(thm)], ['49', '52', '55'])).
% 0.60/0.84  thf('57', plain,
% 0.60/0.84      (![X0 : $i, X2 : $i]:
% 0.60/0.84         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.60/0.84      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.60/0.84  thf('58', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         (~ (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 0.60/0.84          | ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['56', '57'])).
% 0.60/0.84  thf('59', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1))),
% 0.60/0.84      inference('demod', [status(thm)], ['49', '52', '55'])).
% 0.60/0.84  thf('60', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.60/0.84      inference('demod', [status(thm)], ['58', '59'])).
% 0.60/0.84  thf('61', plain,
% 0.60/0.84      (((k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C))
% 0.60/0.84         = (k10_relat_1 @ sk_A @ sk_C))),
% 0.60/0.84      inference('demod', [status(thm)], ['42', '60'])).
% 0.60/0.84  thf('62', plain,
% 0.60/0.84      ((((k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C)
% 0.60/0.84          = (k10_relat_1 @ sk_A @ sk_C))
% 0.60/0.84        | ~ (v1_relat_1 @ sk_A))),
% 0.60/0.84      inference('sup+', [status(thm)], ['0', '61'])).
% 0.60/0.84  thf('63', plain, ((v1_relat_1 @ sk_A)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('64', plain,
% 0.60/0.84      (((k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C)
% 0.60/0.84         = (k10_relat_1 @ sk_A @ sk_C))),
% 0.60/0.84      inference('demod', [status(thm)], ['62', '63'])).
% 0.60/0.84  thf('65', plain,
% 0.60/0.84      (((k10_relat_1 @ sk_A @ sk_C)
% 0.60/0.84         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('66', plain, ($false),
% 0.60/0.84      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 0.60/0.84  
% 0.60/0.84  % SZS output end Refutation
% 0.60/0.84  
% 0.60/0.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
