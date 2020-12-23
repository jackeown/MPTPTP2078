%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.w64UHHkJGY

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:50 EST 2020

% Result     : Theorem 2.82s
% Output     : Refutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :  138 (1304 expanded)
%              Number of leaves         :   28 ( 455 expanded)
%              Depth                    :   27
%              Number of atoms          : 1188 (12008 expanded)
%              Number of equality atoms :   92 ( 943 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('0',plain,(
    ! [X32: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X32 ) )
      = X32 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t189_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ B ) )
            = ( k7_relat_1 @ A @ ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v1_relat_1 @ X30 )
      | ( ( k7_relat_1 @ X31 @ ( k1_relat_1 @ X30 ) )
        = ( k7_relat_1 @ X31 @ ( k1_relat_1 @ ( k7_relat_1 @ X30 @ ( k1_relat_1 @ X31 ) ) ) ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t189_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ X1 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X42: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ X1 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('5',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k7_relat_1 @ X41 @ X40 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X40 ) @ X41 ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('6',plain,(
    ! [X36: $i,X37: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X36 @ X37 ) ) @ X37 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('7',plain,(
    ! [X33: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X33 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('8',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X34 ) @ X35 )
      | ( ( k5_relat_1 @ X34 @ ( k6_relat_1 @ X35 ) )
        = X34 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X42: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','12'])).

thf('14',plain,(
    ! [X42: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('19',plain,(
    ! [X32: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X32 ) )
      = X32 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t89_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ) )).

thf('20',plain,(
    ! [X38: $i,X39: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X38 @ X39 ) ) @ ( k1_relat_1 @ X38 ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t89_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X42: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','25'])).

thf('27',plain,(
    ! [X32: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X32 ) )
      = X32 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_tarski @ X3 @ X2 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k7_relat_1 @ X41 @ X40 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X40 ) @ X41 ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X42: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('42',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X25 @ X26 ) )
        = ( k9_relat_1 @ X25 @ X26 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X33: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X33 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('45',plain,(
    ! [X32: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X32 ) )
      = X32 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t145_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k9_relat_1 @ B @ A )
        = ( k9_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('46',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k9_relat_1 @ X22 @ X23 )
        = ( k9_relat_1 @ X22 @ ( k3_xboole_0 @ ( k1_relat_1 @ X22 ) @ X23 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t145_relat_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X42: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X42: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44','49','50'])).

thf('52',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X25 @ X26 ) )
        = ( k9_relat_1 @ X25 @ X26 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('53',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X34 ) @ X35 )
      | ( ( k5_relat_1 @ X34 @ ( k6_relat_1 @ X35 ) )
        = X34 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k6_relat_1 @ X2 ) )
        = ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X2 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X42: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X2 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X32: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X32 ) )
      = X32 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ X1 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('60',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X42: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['58','63'])).

thf('65',plain,(
    ! [X42: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X2 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['57','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','67'])).

thf('69',plain,(
    ! [X42: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['26','27','68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['26','27','68','69'])).

thf('72',plain,(
    ! [X33: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X33 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['26','27','68','69'])).

thf('75',plain,(
    ! [X32: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X32 ) )
      = X32 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['26','27','68','69'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','67'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['26','27','68','69'])).

thf('82',plain,(
    ! [X42: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['78','79','80','81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['78','79','80','81','82'])).

thf('85',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X25 @ X26 ) )
        = ( k9_relat_1 @ X25 @ X26 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44','49','50'])).

thf('88',plain,(
    ! [X42: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['73','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['70','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['17','92'])).

thf('94',plain,(
    ! [X32: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X32 ) )
      = X32 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X32: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X32 ) )
      = X32 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k7_relat_1 @ X41 @ X40 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X40 ) @ X41 ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t37_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) )
          = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t37_funct_1])).

thf('99',plain,(
    ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
 != ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('101',plain,(
    ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
     != ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['98','101'])).

thf('103',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
 != ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
     != ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['97','104'])).

thf('106',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    $false ),
    inference(simplify,[status(thm)],['107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.w64UHHkJGY
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:11:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 2.82/3.04  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.82/3.04  % Solved by: fo/fo7.sh
% 2.82/3.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.82/3.04  % done 2504 iterations in 2.591s
% 2.82/3.04  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.82/3.04  % SZS output start Refutation
% 2.82/3.04  thf(sk_A_type, type, sk_A: $i).
% 2.82/3.04  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.82/3.04  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.82/3.04  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.82/3.04  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.82/3.04  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 2.82/3.04  thf(sk_B_type, type, sk_B: $i).
% 2.82/3.04  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 2.82/3.04  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.82/3.04  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.82/3.04  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.82/3.04  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 2.82/3.04  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.82/3.04  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.82/3.04  thf(t71_relat_1, axiom,
% 2.82/3.04    (![A:$i]:
% 2.82/3.04     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 2.82/3.04       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 2.82/3.04  thf('0', plain, (![X32 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X32)) = (X32))),
% 2.82/3.04      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.82/3.04  thf(t189_relat_1, axiom,
% 2.82/3.04    (![A:$i]:
% 2.82/3.04     ( ( v1_relat_1 @ A ) =>
% 2.82/3.04       ( ![B:$i]:
% 2.82/3.04         ( ( v1_relat_1 @ B ) =>
% 2.82/3.04           ( ( k7_relat_1 @ A @ ( k1_relat_1 @ B ) ) =
% 2.82/3.04             ( k7_relat_1 @
% 2.82/3.04               A @ ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ))).
% 2.82/3.04  thf('1', plain,
% 2.82/3.04      (![X30 : $i, X31 : $i]:
% 2.82/3.04         (~ (v1_relat_1 @ X30)
% 2.82/3.04          | ((k7_relat_1 @ X31 @ (k1_relat_1 @ X30))
% 2.82/3.04              = (k7_relat_1 @ X31 @ 
% 2.82/3.04                 (k1_relat_1 @ (k7_relat_1 @ X30 @ (k1_relat_1 @ X31)))))
% 2.82/3.04          | ~ (v1_relat_1 @ X31))),
% 2.82/3.04      inference('cnf', [status(esa)], [t189_relat_1])).
% 2.82/3.04  thf('2', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         (((k7_relat_1 @ (k6_relat_1 @ X0) @ (k1_relat_1 @ X1))
% 2.82/3.04            = (k7_relat_1 @ (k6_relat_1 @ X0) @ 
% 2.82/3.04               (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 2.82/3.04          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.82/3.04          | ~ (v1_relat_1 @ X1))),
% 2.82/3.04      inference('sup+', [status(thm)], ['0', '1'])).
% 2.82/3.04  thf(fc3_funct_1, axiom,
% 2.82/3.04    (![A:$i]:
% 2.82/3.04     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 2.82/3.04       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 2.82/3.04  thf('3', plain, (![X42 : $i]: (v1_relat_1 @ (k6_relat_1 @ X42))),
% 2.82/3.04      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.82/3.04  thf('4', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         (((k7_relat_1 @ (k6_relat_1 @ X0) @ (k1_relat_1 @ X1))
% 2.82/3.04            = (k7_relat_1 @ (k6_relat_1 @ X0) @ 
% 2.82/3.04               (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 2.82/3.04          | ~ (v1_relat_1 @ X1))),
% 2.82/3.04      inference('demod', [status(thm)], ['2', '3'])).
% 2.82/3.04  thf(t94_relat_1, axiom,
% 2.82/3.04    (![A:$i,B:$i]:
% 2.82/3.04     ( ( v1_relat_1 @ B ) =>
% 2.82/3.04       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 2.82/3.04  thf('5', plain,
% 2.82/3.04      (![X40 : $i, X41 : $i]:
% 2.82/3.04         (((k7_relat_1 @ X41 @ X40) = (k5_relat_1 @ (k6_relat_1 @ X40) @ X41))
% 2.82/3.04          | ~ (v1_relat_1 @ X41))),
% 2.82/3.04      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.82/3.04  thf(t87_relat_1, axiom,
% 2.82/3.04    (![A:$i,B:$i]:
% 2.82/3.04     ( ( v1_relat_1 @ B ) =>
% 2.82/3.04       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 2.82/3.04  thf('6', plain,
% 2.82/3.04      (![X36 : $i, X37 : $i]:
% 2.82/3.04         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X36 @ X37)) @ X37)
% 2.82/3.04          | ~ (v1_relat_1 @ X36))),
% 2.82/3.04      inference('cnf', [status(esa)], [t87_relat_1])).
% 2.82/3.04  thf('7', plain, (![X33 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X33)) = (X33))),
% 2.82/3.04      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.82/3.04  thf(t79_relat_1, axiom,
% 2.82/3.04    (![A:$i,B:$i]:
% 2.82/3.04     ( ( v1_relat_1 @ B ) =>
% 2.82/3.04       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 2.82/3.04         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 2.82/3.04  thf('8', plain,
% 2.82/3.04      (![X34 : $i, X35 : $i]:
% 2.82/3.04         (~ (r1_tarski @ (k2_relat_1 @ X34) @ X35)
% 2.82/3.04          | ((k5_relat_1 @ X34 @ (k6_relat_1 @ X35)) = (X34))
% 2.82/3.04          | ~ (v1_relat_1 @ X34))),
% 2.82/3.04      inference('cnf', [status(esa)], [t79_relat_1])).
% 2.82/3.04  thf('9', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         (~ (r1_tarski @ X0 @ X1)
% 2.82/3.04          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.82/3.04          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 2.82/3.04              = (k6_relat_1 @ X0)))),
% 2.82/3.04      inference('sup-', [status(thm)], ['7', '8'])).
% 2.82/3.04  thf('10', plain, (![X42 : $i]: (v1_relat_1 @ (k6_relat_1 @ X42))),
% 2.82/3.04      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.82/3.04  thf('11', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         (~ (r1_tarski @ X0 @ X1)
% 2.82/3.04          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 2.82/3.04              = (k6_relat_1 @ X0)))),
% 2.82/3.04      inference('demod', [status(thm)], ['9', '10'])).
% 2.82/3.04  thf('12', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         (~ (v1_relat_1 @ X1)
% 2.82/3.04          | ((k5_relat_1 @ 
% 2.82/3.04              (k6_relat_1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))) @ 
% 2.82/3.04              (k6_relat_1 @ X0))
% 2.82/3.04              = (k6_relat_1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))))),
% 2.82/3.04      inference('sup-', [status(thm)], ['6', '11'])).
% 2.82/3.04  thf('13', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         (((k7_relat_1 @ (k6_relat_1 @ X0) @ 
% 2.82/3.04            (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 2.82/3.04            = (k6_relat_1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 2.82/3.04          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.82/3.04          | ~ (v1_relat_1 @ X1))),
% 2.82/3.04      inference('sup+', [status(thm)], ['5', '12'])).
% 2.82/3.04  thf('14', plain, (![X42 : $i]: (v1_relat_1 @ (k6_relat_1 @ X42))),
% 2.82/3.04      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.82/3.04  thf('15', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         (((k7_relat_1 @ (k6_relat_1 @ X0) @ 
% 2.82/3.04            (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 2.82/3.04            = (k6_relat_1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 2.82/3.04          | ~ (v1_relat_1 @ X1))),
% 2.82/3.04      inference('demod', [status(thm)], ['13', '14'])).
% 2.82/3.04  thf('16', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         (((k7_relat_1 @ (k6_relat_1 @ X1) @ (k1_relat_1 @ X0))
% 2.82/3.04            = (k6_relat_1 @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1))))
% 2.82/3.04          | ~ (v1_relat_1 @ X0)
% 2.82/3.04          | ~ (v1_relat_1 @ X0))),
% 2.82/3.04      inference('sup+', [status(thm)], ['4', '15'])).
% 2.82/3.04  thf('17', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         (~ (v1_relat_1 @ X0)
% 2.82/3.04          | ((k7_relat_1 @ (k6_relat_1 @ X1) @ (k1_relat_1 @ X0))
% 2.82/3.04              = (k6_relat_1 @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)))))),
% 2.82/3.04      inference('simplify', [status(thm)], ['16'])).
% 2.82/3.04  thf('18', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         (~ (v1_relat_1 @ X0)
% 2.82/3.04          | ((k7_relat_1 @ (k6_relat_1 @ X1) @ (k1_relat_1 @ X0))
% 2.82/3.04              = (k6_relat_1 @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)))))),
% 2.82/3.04      inference('simplify', [status(thm)], ['16'])).
% 2.82/3.04  thf('19', plain, (![X32 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X32)) = (X32))),
% 2.82/3.04      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.82/3.04  thf(t89_relat_1, axiom,
% 2.82/3.04    (![A:$i,B:$i]:
% 2.82/3.04     ( ( v1_relat_1 @ B ) =>
% 2.82/3.04       ( r1_tarski @
% 2.82/3.04         ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ))).
% 2.82/3.04  thf('20', plain,
% 2.82/3.04      (![X38 : $i, X39 : $i]:
% 2.82/3.04         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X38 @ X39)) @ 
% 2.82/3.04           (k1_relat_1 @ X38))
% 2.82/3.04          | ~ (v1_relat_1 @ X38))),
% 2.82/3.04      inference('cnf', [status(esa)], [t89_relat_1])).
% 2.82/3.04  thf('21', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1)) @ 
% 2.82/3.04           X0)
% 2.82/3.04          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.82/3.04      inference('sup+', [status(thm)], ['19', '20'])).
% 2.82/3.04  thf('22', plain, (![X42 : $i]: (v1_relat_1 @ (k6_relat_1 @ X42))),
% 2.82/3.04      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.82/3.04  thf('23', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1)) @ X0)),
% 2.82/3.04      inference('demod', [status(thm)], ['21', '22'])).
% 2.82/3.04  thf('24', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         (~ (r1_tarski @ X0 @ X1)
% 2.82/3.04          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 2.82/3.04              = (k6_relat_1 @ X0)))),
% 2.82/3.04      inference('demod', [status(thm)], ['9', '10'])).
% 2.82/3.04  thf('25', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         ((k5_relat_1 @ 
% 2.82/3.04           (k6_relat_1 @ (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))) @ 
% 2.82/3.04           (k6_relat_1 @ X0))
% 2.82/3.04           = (k6_relat_1 @ (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))))),
% 2.82/3.04      inference('sup-', [status(thm)], ['23', '24'])).
% 2.82/3.04  thf('26', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         (((k5_relat_1 @ 
% 2.82/3.04            (k7_relat_1 @ (k6_relat_1 @ X1) @ (k1_relat_1 @ (k6_relat_1 @ X0))) @ 
% 2.82/3.04            (k6_relat_1 @ X0))
% 2.82/3.04            = (k6_relat_1 @ 
% 2.82/3.04               (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))))
% 2.82/3.04          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.82/3.04      inference('sup+', [status(thm)], ['18', '25'])).
% 2.82/3.04  thf('27', plain, (![X32 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X32)) = (X32))),
% 2.82/3.04      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.82/3.04  thf(commutativity_k2_tarski, axiom,
% 2.82/3.04    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 2.82/3.04  thf('28', plain,
% 2.82/3.04      (![X2 : $i, X3 : $i]: ((k2_tarski @ X3 @ X2) = (k2_tarski @ X2 @ X3))),
% 2.82/3.04      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 2.82/3.04  thf(t12_setfam_1, axiom,
% 2.82/3.04    (![A:$i,B:$i]:
% 2.82/3.04     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.82/3.04  thf('29', plain,
% 2.82/3.04      (![X18 : $i, X19 : $i]:
% 2.82/3.04         ((k1_setfam_1 @ (k2_tarski @ X18 @ X19)) = (k3_xboole_0 @ X18 @ X19))),
% 2.82/3.04      inference('cnf', [status(esa)], [t12_setfam_1])).
% 2.82/3.04  thf('30', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 2.82/3.04      inference('sup+', [status(thm)], ['28', '29'])).
% 2.82/3.04  thf('31', plain,
% 2.82/3.04      (![X18 : $i, X19 : $i]:
% 2.82/3.04         ((k1_setfam_1 @ (k2_tarski @ X18 @ X19)) = (k3_xboole_0 @ X18 @ X19))),
% 2.82/3.04      inference('cnf', [status(esa)], [t12_setfam_1])).
% 2.82/3.04  thf('32', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.82/3.04      inference('sup+', [status(thm)], ['30', '31'])).
% 2.82/3.04  thf(t17_xboole_1, axiom,
% 2.82/3.04    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 2.82/3.04  thf('33', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 2.82/3.04      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.82/3.04  thf('34', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 2.82/3.04      inference('sup+', [status(thm)], ['32', '33'])).
% 2.82/3.04  thf('35', plain,
% 2.82/3.04      (![X40 : $i, X41 : $i]:
% 2.82/3.04         (((k7_relat_1 @ X41 @ X40) = (k5_relat_1 @ (k6_relat_1 @ X40) @ X41))
% 2.82/3.04          | ~ (v1_relat_1 @ X41))),
% 2.82/3.04      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.82/3.04  thf('36', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 2.82/3.04      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.82/3.04  thf('37', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         (~ (r1_tarski @ X0 @ X1)
% 2.82/3.04          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 2.82/3.04              = (k6_relat_1 @ X0)))),
% 2.82/3.04      inference('demod', [status(thm)], ['9', '10'])).
% 2.82/3.04  thf('38', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 2.82/3.04           (k6_relat_1 @ X0)) = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.82/3.04      inference('sup-', [status(thm)], ['36', '37'])).
% 2.82/3.04  thf('39', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         (((k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 2.82/3.04            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 2.82/3.04          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 2.82/3.04      inference('sup+', [status(thm)], ['35', '38'])).
% 2.82/3.04  thf('40', plain, (![X42 : $i]: (v1_relat_1 @ (k6_relat_1 @ X42))),
% 2.82/3.04      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.82/3.04  thf('41', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         ((k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 2.82/3.04           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.82/3.04      inference('demod', [status(thm)], ['39', '40'])).
% 2.82/3.04  thf(t148_relat_1, axiom,
% 2.82/3.04    (![A:$i,B:$i]:
% 2.82/3.04     ( ( v1_relat_1 @ B ) =>
% 2.82/3.04       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 2.82/3.04  thf('42', plain,
% 2.82/3.04      (![X25 : $i, X26 : $i]:
% 2.82/3.04         (((k2_relat_1 @ (k7_relat_1 @ X25 @ X26)) = (k9_relat_1 @ X25 @ X26))
% 2.82/3.04          | ~ (v1_relat_1 @ X25))),
% 2.82/3.04      inference('cnf', [status(esa)], [t148_relat_1])).
% 2.82/3.04  thf('43', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         (((k2_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 2.82/3.04            = (k9_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0)))
% 2.82/3.04          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 2.82/3.04      inference('sup+', [status(thm)], ['41', '42'])).
% 2.82/3.04  thf('44', plain, (![X33 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X33)) = (X33))),
% 2.82/3.04      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.82/3.04  thf('45', plain, (![X32 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X32)) = (X32))),
% 2.82/3.04      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.82/3.04  thf(t145_relat_1, axiom,
% 2.82/3.04    (![A:$i,B:$i]:
% 2.82/3.04     ( ( v1_relat_1 @ B ) =>
% 2.82/3.04       ( ( k9_relat_1 @ B @ A ) =
% 2.82/3.04         ( k9_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 2.82/3.04  thf('46', plain,
% 2.82/3.04      (![X22 : $i, X23 : $i]:
% 2.82/3.04         (((k9_relat_1 @ X22 @ X23)
% 2.82/3.04            = (k9_relat_1 @ X22 @ (k3_xboole_0 @ (k1_relat_1 @ X22) @ X23)))
% 2.82/3.04          | ~ (v1_relat_1 @ X22))),
% 2.82/3.04      inference('cnf', [status(esa)], [t145_relat_1])).
% 2.82/3.04  thf('47', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         (((k9_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 2.82/3.04            = (k9_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))
% 2.82/3.04          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.82/3.04      inference('sup+', [status(thm)], ['45', '46'])).
% 2.82/3.04  thf('48', plain, (![X42 : $i]: (v1_relat_1 @ (k6_relat_1 @ X42))),
% 2.82/3.04      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.82/3.04  thf('49', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         ((k9_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 2.82/3.04           = (k9_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 2.82/3.04      inference('demod', [status(thm)], ['47', '48'])).
% 2.82/3.04  thf('50', plain, (![X42 : $i]: (v1_relat_1 @ (k6_relat_1 @ X42))),
% 2.82/3.04      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.82/3.04  thf('51', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         ((k3_xboole_0 @ X1 @ X0) = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 2.82/3.04      inference('demod', [status(thm)], ['43', '44', '49', '50'])).
% 2.82/3.04  thf('52', plain,
% 2.82/3.04      (![X25 : $i, X26 : $i]:
% 2.82/3.04         (((k2_relat_1 @ (k7_relat_1 @ X25 @ X26)) = (k9_relat_1 @ X25 @ X26))
% 2.82/3.04          | ~ (v1_relat_1 @ X25))),
% 2.82/3.04      inference('cnf', [status(esa)], [t148_relat_1])).
% 2.82/3.04  thf('53', plain,
% 2.82/3.04      (![X34 : $i, X35 : $i]:
% 2.82/3.04         (~ (r1_tarski @ (k2_relat_1 @ X34) @ X35)
% 2.82/3.04          | ((k5_relat_1 @ X34 @ (k6_relat_1 @ X35)) = (X34))
% 2.82/3.04          | ~ (v1_relat_1 @ X34))),
% 2.82/3.04      inference('cnf', [status(esa)], [t79_relat_1])).
% 2.82/3.04  thf('54', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.82/3.04         (~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)
% 2.82/3.04          | ~ (v1_relat_1 @ X1)
% 2.82/3.04          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 2.82/3.04          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k6_relat_1 @ X2))
% 2.82/3.04              = (k7_relat_1 @ X1 @ X0)))),
% 2.82/3.04      inference('sup-', [status(thm)], ['52', '53'])).
% 2.82/3.04  thf('55', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.82/3.04         (~ (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 2.82/3.04          | ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 2.82/3.04              (k6_relat_1 @ X2)) = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.82/3.04          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.82/3.04          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 2.82/3.04      inference('sup-', [status(thm)], ['51', '54'])).
% 2.82/3.04  thf('56', plain, (![X42 : $i]: (v1_relat_1 @ (k6_relat_1 @ X42))),
% 2.82/3.04      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.82/3.04  thf('57', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.82/3.04         (~ (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 2.82/3.04          | ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 2.82/3.04              (k6_relat_1 @ X2)) = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.82/3.04          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 2.82/3.04      inference('demod', [status(thm)], ['55', '56'])).
% 2.82/3.04  thf('58', plain, (![X32 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X32)) = (X32))),
% 2.82/3.04      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.82/3.04  thf('59', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         (((k7_relat_1 @ (k6_relat_1 @ X0) @ (k1_relat_1 @ X1))
% 2.82/3.04            = (k7_relat_1 @ (k6_relat_1 @ X0) @ 
% 2.82/3.04               (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 2.82/3.04          | ~ (v1_relat_1 @ X1))),
% 2.82/3.04      inference('demod', [status(thm)], ['2', '3'])).
% 2.82/3.04  thf(dt_k7_relat_1, axiom,
% 2.82/3.04    (![A:$i,B:$i]:
% 2.82/3.04     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 2.82/3.04  thf('60', plain,
% 2.82/3.04      (![X20 : $i, X21 : $i]:
% 2.82/3.04         (~ (v1_relat_1 @ X20) | (v1_relat_1 @ (k7_relat_1 @ X20 @ X21)))),
% 2.82/3.04      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 2.82/3.04  thf('61', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         ((v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ (k1_relat_1 @ X0)))
% 2.82/3.04          | ~ (v1_relat_1 @ X0)
% 2.82/3.04          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 2.82/3.04      inference('sup+', [status(thm)], ['59', '60'])).
% 2.82/3.04  thf('62', plain, (![X42 : $i]: (v1_relat_1 @ (k6_relat_1 @ X42))),
% 2.82/3.04      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.82/3.04  thf('63', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         ((v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ (k1_relat_1 @ X0)))
% 2.82/3.04          | ~ (v1_relat_1 @ X0))),
% 2.82/3.04      inference('demod', [status(thm)], ['61', '62'])).
% 2.82/3.04  thf('64', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         ((v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.82/3.04          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.82/3.04      inference('sup+', [status(thm)], ['58', '63'])).
% 2.82/3.04  thf('65', plain, (![X42 : $i]: (v1_relat_1 @ (k6_relat_1 @ X42))),
% 2.82/3.04      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.82/3.04  thf('66', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 2.82/3.04      inference('demod', [status(thm)], ['64', '65'])).
% 2.82/3.04  thf('67', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.82/3.04         (~ (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 2.82/3.04          | ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 2.82/3.04              (k6_relat_1 @ X2)) = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 2.82/3.04      inference('demod', [status(thm)], ['57', '66'])).
% 2.82/3.04  thf('68', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 2.82/3.04           (k6_relat_1 @ X0)) = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 2.82/3.04      inference('sup-', [status(thm)], ['34', '67'])).
% 2.82/3.04  thf('69', plain, (![X42 : $i]: (v1_relat_1 @ (k6_relat_1 @ X42))),
% 2.82/3.04      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.82/3.04  thf('70', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 2.82/3.04           = (k6_relat_1 @ (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))))),
% 2.82/3.04      inference('demod', [status(thm)], ['26', '27', '68', '69'])).
% 2.82/3.04  thf('71', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 2.82/3.04           = (k6_relat_1 @ (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))))),
% 2.82/3.04      inference('demod', [status(thm)], ['26', '27', '68', '69'])).
% 2.82/3.04  thf('72', plain, (![X33 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X33)) = (X33))),
% 2.82/3.04      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.82/3.04  thf('73', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         ((k2_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.82/3.04           = (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 2.82/3.04      inference('sup+', [status(thm)], ['71', '72'])).
% 2.82/3.04  thf('74', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 2.82/3.04           = (k6_relat_1 @ (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))))),
% 2.82/3.04      inference('demod', [status(thm)], ['26', '27', '68', '69'])).
% 2.82/3.04  thf('75', plain, (![X32 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X32)) = (X32))),
% 2.82/3.04      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.82/3.04  thf('76', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.82/3.04           = (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 2.82/3.04      inference('sup+', [status(thm)], ['74', '75'])).
% 2.82/3.04  thf('77', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         (~ (v1_relat_1 @ X1)
% 2.82/3.04          | ((k5_relat_1 @ 
% 2.82/3.04              (k6_relat_1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))) @ 
% 2.82/3.04              (k6_relat_1 @ X0))
% 2.82/3.04              = (k6_relat_1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))))),
% 2.82/3.04      inference('sup-', [status(thm)], ['6', '11'])).
% 2.82/3.04  thf('78', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         (((k5_relat_1 @ 
% 2.82/3.04            (k6_relat_1 @ (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))) @ 
% 2.82/3.04            (k6_relat_1 @ X1))
% 2.82/3.04            = (k6_relat_1 @ 
% 2.82/3.04               (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))))
% 2.82/3.04          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.82/3.04      inference('sup+', [status(thm)], ['76', '77'])).
% 2.82/3.04  thf('79', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 2.82/3.04           = (k6_relat_1 @ (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))))),
% 2.82/3.04      inference('demod', [status(thm)], ['26', '27', '68', '69'])).
% 2.82/3.04  thf('80', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         ((k5_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 2.82/3.04           (k6_relat_1 @ X0)) = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 2.82/3.04      inference('sup-', [status(thm)], ['34', '67'])).
% 2.82/3.04  thf('81', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 2.82/3.04           = (k6_relat_1 @ (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))))),
% 2.82/3.04      inference('demod', [status(thm)], ['26', '27', '68', '69'])).
% 2.82/3.04  thf('82', plain, (![X42 : $i]: (v1_relat_1 @ (k6_relat_1 @ X42))),
% 2.82/3.04      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.82/3.04  thf('83', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 2.82/3.04           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 2.82/3.04      inference('demod', [status(thm)], ['78', '79', '80', '81', '82'])).
% 2.82/3.04  thf('84', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 2.82/3.04           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 2.82/3.04      inference('demod', [status(thm)], ['78', '79', '80', '81', '82'])).
% 2.82/3.04  thf('85', plain,
% 2.82/3.04      (![X25 : $i, X26 : $i]:
% 2.82/3.04         (((k2_relat_1 @ (k7_relat_1 @ X25 @ X26)) = (k9_relat_1 @ X25 @ X26))
% 2.82/3.04          | ~ (v1_relat_1 @ X25))),
% 2.82/3.04      inference('cnf', [status(esa)], [t148_relat_1])).
% 2.82/3.04  thf('86', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         (((k2_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.82/3.04            = (k9_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 2.82/3.04          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.82/3.04      inference('sup+', [status(thm)], ['84', '85'])).
% 2.82/3.04  thf('87', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         ((k3_xboole_0 @ X1 @ X0) = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 2.82/3.04      inference('demod', [status(thm)], ['43', '44', '49', '50'])).
% 2.82/3.04  thf('88', plain, (![X42 : $i]: (v1_relat_1 @ (k6_relat_1 @ X42))),
% 2.82/3.04      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.82/3.04  thf('89', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         ((k2_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.82/3.04           = (k3_xboole_0 @ X0 @ X1))),
% 2.82/3.04      inference('demod', [status(thm)], ['86', '87', '88'])).
% 2.82/3.04  thf('90', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         ((k2_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.82/3.04           = (k3_xboole_0 @ X1 @ X0))),
% 2.82/3.04      inference('sup+', [status(thm)], ['83', '89'])).
% 2.82/3.04  thf('91', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         ((k3_xboole_0 @ X1 @ X0)
% 2.82/3.04           = (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 2.82/3.04      inference('demod', [status(thm)], ['73', '90'])).
% 2.82/3.04  thf('92', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 2.82/3.04           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.82/3.04      inference('demod', [status(thm)], ['70', '91'])).
% 2.82/3.04  thf('93', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         (~ (v1_relat_1 @ X0)
% 2.82/3.04          | ((k6_relat_1 @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)))
% 2.82/3.04              = (k6_relat_1 @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)))))),
% 2.82/3.04      inference('demod', [status(thm)], ['17', '92'])).
% 2.82/3.04  thf('94', plain, (![X32 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X32)) = (X32))),
% 2.82/3.04      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.82/3.04  thf('95', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         (((k1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0))))
% 2.82/3.04            = (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)))
% 2.82/3.04          | ~ (v1_relat_1 @ X0))),
% 2.82/3.04      inference('sup+', [status(thm)], ['93', '94'])).
% 2.82/3.04  thf('96', plain, (![X32 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X32)) = (X32))),
% 2.82/3.04      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.82/3.04  thf('97', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]:
% 2.82/3.04         (((k3_xboole_0 @ X1 @ (k1_relat_1 @ X0))
% 2.82/3.04            = (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)))
% 2.82/3.04          | ~ (v1_relat_1 @ X0))),
% 2.82/3.04      inference('demod', [status(thm)], ['95', '96'])).
% 2.82/3.04  thf('98', plain,
% 2.82/3.04      (![X40 : $i, X41 : $i]:
% 2.82/3.04         (((k7_relat_1 @ X41 @ X40) = (k5_relat_1 @ (k6_relat_1 @ X40) @ X41))
% 2.82/3.04          | ~ (v1_relat_1 @ X41))),
% 2.82/3.04      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.82/3.04  thf(t37_funct_1, conjecture,
% 2.82/3.04    (![A:$i,B:$i]:
% 2.82/3.04     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.82/3.04       ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) =
% 2.82/3.04         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 2.82/3.04  thf(zf_stmt_0, negated_conjecture,
% 2.82/3.04    (~( ![A:$i,B:$i]:
% 2.82/3.04        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.82/3.04          ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) =
% 2.82/3.04            ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )),
% 2.82/3.04    inference('cnf.neg', [status(esa)], [t37_funct_1])).
% 2.82/3.04  thf('99', plain,
% 2.82/3.04      (((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))
% 2.82/3.04         != (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 2.82/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.04  thf('100', plain,
% 2.82/3.04      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.82/3.04      inference('sup+', [status(thm)], ['30', '31'])).
% 2.82/3.04  thf('101', plain,
% 2.82/3.04      (((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))
% 2.82/3.04         != (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 2.82/3.04      inference('demod', [status(thm)], ['99', '100'])).
% 2.82/3.04  thf('102', plain,
% 2.82/3.04      ((((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))
% 2.82/3.04          != (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))
% 2.82/3.04        | ~ (v1_relat_1 @ sk_B))),
% 2.82/3.04      inference('sup-', [status(thm)], ['98', '101'])).
% 2.82/3.04  thf('103', plain, ((v1_relat_1 @ sk_B)),
% 2.82/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.04  thf('104', plain,
% 2.82/3.04      (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))
% 2.82/3.04         != (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 2.82/3.04      inference('demod', [status(thm)], ['102', '103'])).
% 2.82/3.04  thf('105', plain,
% 2.82/3.04      ((((k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B))
% 2.82/3.04          != (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))
% 2.82/3.04        | ~ (v1_relat_1 @ sk_B))),
% 2.82/3.04      inference('sup-', [status(thm)], ['97', '104'])).
% 2.82/3.04  thf('106', plain, ((v1_relat_1 @ sk_B)),
% 2.82/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.04  thf('107', plain,
% 2.82/3.04      (((k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B))
% 2.82/3.04         != (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 2.82/3.04      inference('demod', [status(thm)], ['105', '106'])).
% 2.82/3.04  thf('108', plain, ($false), inference('simplify', [status(thm)], ['107'])).
% 2.82/3.04  
% 2.82/3.04  % SZS output end Refutation
% 2.82/3.04  
% 2.82/3.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
