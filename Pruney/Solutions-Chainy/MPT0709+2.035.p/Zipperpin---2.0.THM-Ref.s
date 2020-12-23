%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YFL1qu778L

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:10 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :  208 ( 596 expanded)
%              Number of leaves         :   21 ( 188 expanded)
%              Depth                    :   34
%              Number of atoms          : 1892 (7098 expanded)
%              Number of equality atoms :   54 ( 307 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('1',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('2',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k10_relat_1 @ X15 @ X16 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X15 ) @ X16 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X3: $i] :
      ( ( ( k9_relat_1 @ X3 @ ( k1_relat_1 @ X3 ) )
        = ( k2_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X3: $i] :
      ( ( ( k9_relat_1 @ X3 @ ( k1_relat_1 @ X3 ) )
        = ( k2_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('9',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t154_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k9_relat_1 @ B @ A )
          = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k9_relat_1 @ X13 @ X14 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X13 ) @ X14 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X4 @ X5 ) @ ( k1_relat_1 @ X4 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t178_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('17',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( r1_tarski @ ( k10_relat_1 @ X9 @ X7 ) @ ( k10_relat_1 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t178_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('19',plain,(
    ! [X6: $i] :
      ( ( ( k10_relat_1 @ X6 @ ( k2_relat_1 @ X6 ) )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('20',plain,(
    ! [X3: $i] :
      ( ( ( k9_relat_1 @ X3 @ ( k1_relat_1 @ X3 ) )
        = ( k2_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('21',plain,(
    ! [X3: $i] :
      ( ( ( k9_relat_1 @ X3 @ ( k1_relat_1 @ X3 ) )
        = ( k2_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('22',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k9_relat_1 @ X13 @ X14 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X13 ) @ X14 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('23',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('24',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k9_relat_1 @ X13 @ X14 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X13 ) @ X14 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('25',plain,(
    ! [X6: $i] :
      ( ( ( k10_relat_1 @ X6 @ ( k2_relat_1 @ X6 ) )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('26',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X4 @ X5 ) @ ( k1_relat_1 @ X4 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( r1_tarski @ ( k10_relat_1 @ X9 @ X7 ) @ ( k10_relat_1 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t178_relat_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ X1 ) @ ( k1_relat_1 @ X0 ) ) @ ( k9_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X1 ) ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['23','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X1 ) ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k9_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k9_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( r1_tarski @ ( k10_relat_1 @ X9 @ X7 ) @ ( k10_relat_1 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t178_relat_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf(t164_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
            & ( v2_funct_1 @ B ) )
         => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t164_funct_1])).

thf('44',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','48','49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['18','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['54','55','56','57','58'])).

thf('60',plain,
    ( ( r1_tarski @ sk_A @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['60','61','62','63'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('65',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X11 @ ( k2_relat_1 @ X12 ) )
      | ( ( k9_relat_1 @ X12 @ ( k10_relat_1 @ X12 @ X11 ) )
        = X11 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('66',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k9_relat_1 @ X13 @ X14 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X13 ) @ X14 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('68',plain,(
    ! [X3: $i] :
      ( ( ( k9_relat_1 @ X3 @ ( k1_relat_1 @ X3 ) )
        = ( k2_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('69',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('70',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k9_relat_1 @ X13 @ X14 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X13 ) @ X14 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('71',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( r1_tarski @ ( k10_relat_1 @ X9 @ X7 ) @ ( k10_relat_1 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t178_relat_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ sk_A ) @ ( k10_relat_1 @ X0 @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ sk_A ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ sk_A ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['69','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ sk_A ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['68','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['77','78','79','80','81'])).

thf('83',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X11 @ ( k2_relat_1 @ X12 ) )
      | ( ( k9_relat_1 @ X12 @ ( k10_relat_1 @ X12 @ X11 ) )
        = X11 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('84',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
      = ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
    = ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
      = ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['67','87'])).

thf('89',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k9_relat_1 @ X13 @ X14 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X13 ) @ X14 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('90',plain,(
    r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['77','78','79','80','81'])).

thf('91',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['91','92','93','94'])).

thf('96',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X11 @ ( k2_relat_1 @ X12 ) )
      | ( ( k9_relat_1 @ X12 @ ( k10_relat_1 @ X12 @ X11 ) )
        = X11 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('97',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
      = ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = ( k9_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['88','100','101','102','103'])).

thf('105',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('106',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('109',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['91','92','93','94'])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_B @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( r1_tarski @ ( k9_relat_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['108','111'])).

thf('113',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['112','113','114','115'])).

thf('117',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( r1_tarski @ ( k10_relat_1 @ X9 @ X7 ) @ ( k10_relat_1 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t178_relat_1])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['107','118'])).

thf('120',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['119','120','121','122','123'])).

thf('125',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X11 @ ( k2_relat_1 @ X12 ) )
      | ( ( k9_relat_1 @ X12 @ ( k10_relat_1 @ X12 @ X11 ) )
        = X11 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('126',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) )
      = ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k9_relat_1 @ X13 @ X14 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X13 ) @ X14 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('128',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('129',plain,(
    ! [X3: $i] :
      ( ( ( k9_relat_1 @ X3 @ ( k1_relat_1 @ X3 ) )
        = ( k2_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X1 ) ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    ! [X6: $i] :
      ( ( ( k10_relat_1 @ X6 @ ( k2_relat_1 @ X6 ) )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('134',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['91','92','93','94'])).

thf('135',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( r1_tarski @ ( k10_relat_1 @ X9 @ X7 ) @ ( k10_relat_1 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t178_relat_1])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['133','136'])).

thf('138',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['137','138','139'])).

thf('141',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( r1_tarski @ ( k10_relat_1 @ X9 @ X7 ) @ ( k10_relat_1 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t178_relat_1])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) @ ( k10_relat_1 @ X0 @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) @ X1 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k1_relat_1 @ sk_B ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['132','144'])).

thf('146',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['145','146','147','148'])).

thf('150',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['128','149'])).

thf('151',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['150','151','152'])).

thf('154',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X11 @ ( k2_relat_1 @ X12 ) )
      | ( ( k9_relat_1 @ X12 @ ( k10_relat_1 @ X12 @ X11 ) )
        = X11 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('155',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ) )
      = ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ) )
    = ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['155','156','157'])).

thf('159',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ) )
      = ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['127','158'])).

thf('160',plain,
    ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = ( k9_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('161',plain,
    ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = ( k9_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('162',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['159','160','161','162','163','164'])).

thf('166',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['126','165'])).

thf('167',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['106','166'])).

thf('168',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['167','168','169'])).

thf('171',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['105','170'])).

thf('172',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
    = ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['171','172','173'])).

thf('175',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = sk_A ) ),
    inference(demod,[status(thm)],['66','104','174'])).

thf('176',plain,(
    ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['175','176'])).

thf('178',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','177'])).

thf('179',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['178','179','180'])).

thf('182',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','181'])).

thf('183',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    $false ),
    inference(demod,[status(thm)],['182','183','184'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YFL1qu778L
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:09:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.49/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.49/0.67  % Solved by: fo/fo7.sh
% 0.49/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.67  % done 402 iterations in 0.220s
% 0.49/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.49/0.67  % SZS output start Refutation
% 0.49/0.67  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.49/0.67  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.49/0.67  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.49/0.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.49/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.49/0.67  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.49/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.67  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.49/0.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.49/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.49/0.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.49/0.67  thf(dt_k2_funct_1, axiom,
% 0.49/0.67    (![A:$i]:
% 0.49/0.67     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.49/0.67       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.49/0.67         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.49/0.67  thf('0', plain,
% 0.49/0.67      (![X10 : $i]:
% 0.49/0.67         ((v1_funct_1 @ (k2_funct_1 @ X10))
% 0.49/0.67          | ~ (v1_funct_1 @ X10)
% 0.49/0.67          | ~ (v1_relat_1 @ X10))),
% 0.49/0.67      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.49/0.67  thf('1', plain,
% 0.49/0.67      (![X10 : $i]:
% 0.49/0.67         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 0.49/0.67          | ~ (v1_funct_1 @ X10)
% 0.49/0.67          | ~ (v1_relat_1 @ X10))),
% 0.49/0.67      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.49/0.67  thf('2', plain,
% 0.49/0.67      (![X10 : $i]:
% 0.49/0.67         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 0.49/0.67          | ~ (v1_funct_1 @ X10)
% 0.49/0.67          | ~ (v1_relat_1 @ X10))),
% 0.49/0.67      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.49/0.67  thf(t155_funct_1, axiom,
% 0.49/0.67    (![A:$i,B:$i]:
% 0.49/0.67     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.49/0.67       ( ( v2_funct_1 @ B ) =>
% 0.49/0.67         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.49/0.67  thf('3', plain,
% 0.49/0.67      (![X15 : $i, X16 : $i]:
% 0.49/0.67         (~ (v2_funct_1 @ X15)
% 0.49/0.67          | ((k10_relat_1 @ X15 @ X16)
% 0.49/0.67              = (k9_relat_1 @ (k2_funct_1 @ X15) @ X16))
% 0.49/0.67          | ~ (v1_funct_1 @ X15)
% 0.49/0.67          | ~ (v1_relat_1 @ X15))),
% 0.49/0.67      inference('cnf', [status(esa)], [t155_funct_1])).
% 0.49/0.67  thf(t146_relat_1, axiom,
% 0.49/0.67    (![A:$i]:
% 0.49/0.67     ( ( v1_relat_1 @ A ) =>
% 0.49/0.67       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.49/0.67  thf('4', plain,
% 0.49/0.67      (![X3 : $i]:
% 0.49/0.67         (((k9_relat_1 @ X3 @ (k1_relat_1 @ X3)) = (k2_relat_1 @ X3))
% 0.49/0.67          | ~ (v1_relat_1 @ X3))),
% 0.49/0.67      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.49/0.67  thf('5', plain,
% 0.49/0.67      (![X0 : $i]:
% 0.49/0.67         (((k10_relat_1 @ X0 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.49/0.67            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.49/0.67          | ~ (v1_relat_1 @ X0)
% 0.49/0.67          | ~ (v1_funct_1 @ X0)
% 0.49/0.67          | ~ (v2_funct_1 @ X0)
% 0.49/0.67          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.49/0.67      inference('sup+', [status(thm)], ['3', '4'])).
% 0.49/0.67  thf('6', plain,
% 0.49/0.67      (![X0 : $i]:
% 0.49/0.67         (~ (v1_relat_1 @ X0)
% 0.49/0.67          | ~ (v1_funct_1 @ X0)
% 0.49/0.67          | ~ (v2_funct_1 @ X0)
% 0.49/0.67          | ~ (v1_funct_1 @ X0)
% 0.49/0.67          | ~ (v1_relat_1 @ X0)
% 0.49/0.67          | ((k10_relat_1 @ X0 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.49/0.67              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 0.49/0.67      inference('sup-', [status(thm)], ['2', '5'])).
% 0.49/0.67  thf('7', plain,
% 0.49/0.67      (![X0 : $i]:
% 0.49/0.67         (((k10_relat_1 @ X0 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.49/0.67            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.49/0.67          | ~ (v2_funct_1 @ X0)
% 0.49/0.67          | ~ (v1_funct_1 @ X0)
% 0.49/0.67          | ~ (v1_relat_1 @ X0))),
% 0.49/0.67      inference('simplify', [status(thm)], ['6'])).
% 0.49/0.67  thf('8', plain,
% 0.49/0.67      (![X3 : $i]:
% 0.49/0.67         (((k9_relat_1 @ X3 @ (k1_relat_1 @ X3)) = (k2_relat_1 @ X3))
% 0.49/0.67          | ~ (v1_relat_1 @ X3))),
% 0.49/0.67      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.49/0.67  thf('9', plain,
% 0.49/0.67      (![X10 : $i]:
% 0.49/0.67         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 0.49/0.67          | ~ (v1_funct_1 @ X10)
% 0.49/0.67          | ~ (v1_relat_1 @ X10))),
% 0.49/0.67      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.49/0.67  thf(t154_funct_1, axiom,
% 0.49/0.67    (![A:$i,B:$i]:
% 0.49/0.67     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.49/0.67       ( ( v2_funct_1 @ B ) =>
% 0.49/0.67         ( ( k9_relat_1 @ B @ A ) = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.49/0.67  thf('10', plain,
% 0.49/0.67      (![X13 : $i, X14 : $i]:
% 0.49/0.67         (~ (v2_funct_1 @ X13)
% 0.49/0.67          | ((k9_relat_1 @ X13 @ X14)
% 0.49/0.67              = (k10_relat_1 @ (k2_funct_1 @ X13) @ X14))
% 0.49/0.67          | ~ (v1_funct_1 @ X13)
% 0.49/0.67          | ~ (v1_relat_1 @ X13))),
% 0.49/0.67      inference('cnf', [status(esa)], [t154_funct_1])).
% 0.49/0.67  thf(t167_relat_1, axiom,
% 0.49/0.67    (![A:$i,B:$i]:
% 0.49/0.67     ( ( v1_relat_1 @ B ) =>
% 0.49/0.67       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.49/0.67  thf('11', plain,
% 0.49/0.67      (![X4 : $i, X5 : $i]:
% 0.49/0.67         ((r1_tarski @ (k10_relat_1 @ X4 @ X5) @ (k1_relat_1 @ X4))
% 0.49/0.67          | ~ (v1_relat_1 @ X4))),
% 0.49/0.67      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.49/0.67  thf('12', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((r1_tarski @ (k9_relat_1 @ X1 @ X0) @ 
% 0.49/0.67           (k1_relat_1 @ (k2_funct_1 @ X1)))
% 0.49/0.67          | ~ (v1_relat_1 @ X1)
% 0.49/0.67          | ~ (v1_funct_1 @ X1)
% 0.49/0.67          | ~ (v2_funct_1 @ X1)
% 0.49/0.67          | ~ (v1_relat_1 @ (k2_funct_1 @ X1)))),
% 0.49/0.67      inference('sup+', [status(thm)], ['10', '11'])).
% 0.49/0.67  thf('13', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         (~ (v1_relat_1 @ X0)
% 0.49/0.67          | ~ (v1_funct_1 @ X0)
% 0.49/0.67          | ~ (v2_funct_1 @ X0)
% 0.49/0.67          | ~ (v1_funct_1 @ X0)
% 0.49/0.67          | ~ (v1_relat_1 @ X0)
% 0.49/0.67          | (r1_tarski @ (k9_relat_1 @ X0 @ X1) @ 
% 0.49/0.67             (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 0.49/0.67      inference('sup-', [status(thm)], ['9', '12'])).
% 0.49/0.67  thf('14', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((r1_tarski @ (k9_relat_1 @ X0 @ X1) @ 
% 0.49/0.67           (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.49/0.67          | ~ (v2_funct_1 @ X0)
% 0.49/0.67          | ~ (v1_funct_1 @ X0)
% 0.49/0.67          | ~ (v1_relat_1 @ X0))),
% 0.49/0.67      inference('simplify', [status(thm)], ['13'])).
% 0.49/0.67  thf('15', plain,
% 0.49/0.67      (![X0 : $i]:
% 0.49/0.67         ((r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.49/0.67          | ~ (v1_relat_1 @ X0)
% 0.49/0.67          | ~ (v1_relat_1 @ X0)
% 0.49/0.67          | ~ (v1_funct_1 @ X0)
% 0.49/0.67          | ~ (v2_funct_1 @ X0))),
% 0.49/0.67      inference('sup+', [status(thm)], ['8', '14'])).
% 0.49/0.67  thf('16', plain,
% 0.49/0.67      (![X0 : $i]:
% 0.49/0.67         (~ (v2_funct_1 @ X0)
% 0.49/0.67          | ~ (v1_funct_1 @ X0)
% 0.49/0.67          | ~ (v1_relat_1 @ X0)
% 0.49/0.67          | (r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 0.49/0.67      inference('simplify', [status(thm)], ['15'])).
% 0.49/0.67  thf(t178_relat_1, axiom,
% 0.49/0.67    (![A:$i,B:$i,C:$i]:
% 0.49/0.67     ( ( v1_relat_1 @ C ) =>
% 0.49/0.67       ( ( r1_tarski @ A @ B ) =>
% 0.49/0.67         ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.49/0.67  thf('17', plain,
% 0.49/0.67      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.49/0.67         (~ (r1_tarski @ X7 @ X8)
% 0.49/0.67          | ~ (v1_relat_1 @ X9)
% 0.49/0.67          | (r1_tarski @ (k10_relat_1 @ X9 @ X7) @ (k10_relat_1 @ X9 @ X8)))),
% 0.49/0.67      inference('cnf', [status(esa)], [t178_relat_1])).
% 0.49/0.67  thf('18', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         (~ (v1_relat_1 @ X0)
% 0.49/0.67          | ~ (v1_funct_1 @ X0)
% 0.49/0.67          | ~ (v2_funct_1 @ X0)
% 0.49/0.67          | (r1_tarski @ (k10_relat_1 @ X1 @ (k2_relat_1 @ X0)) @ 
% 0.49/0.67             (k10_relat_1 @ X1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.49/0.67          | ~ (v1_relat_1 @ X1))),
% 0.49/0.67      inference('sup-', [status(thm)], ['16', '17'])).
% 0.49/0.67  thf(t169_relat_1, axiom,
% 0.49/0.67    (![A:$i]:
% 0.49/0.67     ( ( v1_relat_1 @ A ) =>
% 0.49/0.67       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.49/0.67  thf('19', plain,
% 0.49/0.67      (![X6 : $i]:
% 0.49/0.67         (((k10_relat_1 @ X6 @ (k2_relat_1 @ X6)) = (k1_relat_1 @ X6))
% 0.49/0.67          | ~ (v1_relat_1 @ X6))),
% 0.49/0.67      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.49/0.67  thf('20', plain,
% 0.49/0.67      (![X3 : $i]:
% 0.49/0.67         (((k9_relat_1 @ X3 @ (k1_relat_1 @ X3)) = (k2_relat_1 @ X3))
% 0.49/0.67          | ~ (v1_relat_1 @ X3))),
% 0.49/0.67      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.49/0.67  thf('21', plain,
% 0.49/0.67      (![X3 : $i]:
% 0.49/0.67         (((k9_relat_1 @ X3 @ (k1_relat_1 @ X3)) = (k2_relat_1 @ X3))
% 0.49/0.67          | ~ (v1_relat_1 @ X3))),
% 0.49/0.67      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.49/0.67  thf('22', plain,
% 0.49/0.67      (![X13 : $i, X14 : $i]:
% 0.49/0.67         (~ (v2_funct_1 @ X13)
% 0.49/0.67          | ((k9_relat_1 @ X13 @ X14)
% 0.49/0.67              = (k10_relat_1 @ (k2_funct_1 @ X13) @ X14))
% 0.49/0.67          | ~ (v1_funct_1 @ X13)
% 0.49/0.67          | ~ (v1_relat_1 @ X13))),
% 0.49/0.67      inference('cnf', [status(esa)], [t154_funct_1])).
% 0.49/0.67  thf('23', plain,
% 0.49/0.67      (![X10 : $i]:
% 0.49/0.67         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 0.49/0.67          | ~ (v1_funct_1 @ X10)
% 0.49/0.67          | ~ (v1_relat_1 @ X10))),
% 0.49/0.67      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.49/0.67  thf('24', plain,
% 0.49/0.67      (![X13 : $i, X14 : $i]:
% 0.49/0.67         (~ (v2_funct_1 @ X13)
% 0.49/0.67          | ((k9_relat_1 @ X13 @ X14)
% 0.49/0.67              = (k10_relat_1 @ (k2_funct_1 @ X13) @ X14))
% 0.49/0.67          | ~ (v1_funct_1 @ X13)
% 0.49/0.67          | ~ (v1_relat_1 @ X13))),
% 0.49/0.67      inference('cnf', [status(esa)], [t154_funct_1])).
% 0.49/0.67  thf('25', plain,
% 0.49/0.67      (![X6 : $i]:
% 0.49/0.67         (((k10_relat_1 @ X6 @ (k2_relat_1 @ X6)) = (k1_relat_1 @ X6))
% 0.49/0.67          | ~ (v1_relat_1 @ X6))),
% 0.49/0.67      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.49/0.67  thf('26', plain,
% 0.49/0.67      (![X4 : $i, X5 : $i]:
% 0.49/0.67         ((r1_tarski @ (k10_relat_1 @ X4 @ X5) @ (k1_relat_1 @ X4))
% 0.49/0.67          | ~ (v1_relat_1 @ X4))),
% 0.49/0.67      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.49/0.67  thf('27', plain,
% 0.49/0.67      (![X0 : $i]:
% 0.49/0.67         ((r1_tarski @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.49/0.67          | ~ (v1_relat_1 @ X0)
% 0.49/0.67          | ~ (v1_relat_1 @ X0))),
% 0.49/0.67      inference('sup+', [status(thm)], ['25', '26'])).
% 0.49/0.67  thf('28', plain,
% 0.49/0.67      (![X0 : $i]:
% 0.49/0.67         (~ (v1_relat_1 @ X0)
% 0.49/0.67          | (r1_tarski @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.49/0.67      inference('simplify', [status(thm)], ['27'])).
% 0.49/0.67  thf('29', plain,
% 0.49/0.67      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.49/0.67         (~ (r1_tarski @ X7 @ X8)
% 0.49/0.67          | ~ (v1_relat_1 @ X9)
% 0.49/0.67          | (r1_tarski @ (k10_relat_1 @ X9 @ X7) @ (k10_relat_1 @ X9 @ X8)))),
% 0.49/0.67      inference('cnf', [status(esa)], [t178_relat_1])).
% 0.49/0.67  thf('30', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         (~ (v1_relat_1 @ X0)
% 0.49/0.67          | (r1_tarski @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)) @ 
% 0.49/0.67             (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 0.49/0.67          | ~ (v1_relat_1 @ X1))),
% 0.49/0.67      inference('sup-', [status(thm)], ['28', '29'])).
% 0.49/0.67  thf('31', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ X1) @ (k1_relat_1 @ X0)) @ 
% 0.49/0.67           (k9_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 0.49/0.67          | ~ (v1_relat_1 @ X1)
% 0.49/0.67          | ~ (v1_funct_1 @ X1)
% 0.49/0.67          | ~ (v2_funct_1 @ X1)
% 0.49/0.67          | ~ (v1_relat_1 @ (k2_funct_1 @ X1))
% 0.49/0.67          | ~ (v1_relat_1 @ X0))),
% 0.49/0.67      inference('sup+', [status(thm)], ['24', '30'])).
% 0.49/0.67  thf('32', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         (~ (v1_relat_1 @ X0)
% 0.49/0.67          | ~ (v1_funct_1 @ X0)
% 0.49/0.67          | ~ (v1_relat_1 @ X1)
% 0.49/0.67          | ~ (v2_funct_1 @ X0)
% 0.49/0.67          | ~ (v1_funct_1 @ X0)
% 0.49/0.67          | ~ (v1_relat_1 @ X0)
% 0.49/0.67          | (r1_tarski @ 
% 0.49/0.67             (k10_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X1)) @ 
% 0.49/0.67             (k9_relat_1 @ X0 @ (k1_relat_1 @ X1))))),
% 0.49/0.67      inference('sup-', [status(thm)], ['23', '31'])).
% 0.49/0.67  thf('33', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X1)) @ 
% 0.49/0.67           (k9_relat_1 @ X0 @ (k1_relat_1 @ X1)))
% 0.49/0.67          | ~ (v2_funct_1 @ X0)
% 0.49/0.67          | ~ (v1_relat_1 @ X1)
% 0.49/0.67          | ~ (v1_funct_1 @ X0)
% 0.49/0.67          | ~ (v1_relat_1 @ X0))),
% 0.49/0.67      inference('simplify', [status(thm)], ['32'])).
% 0.49/0.67  thf('34', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((r1_tarski @ (k9_relat_1 @ X1 @ (k1_relat_1 @ X0)) @ 
% 0.49/0.67           (k9_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 0.49/0.67          | ~ (v1_relat_1 @ X1)
% 0.49/0.67          | ~ (v1_funct_1 @ X1)
% 0.49/0.67          | ~ (v2_funct_1 @ X1)
% 0.49/0.67          | ~ (v1_relat_1 @ X1)
% 0.49/0.67          | ~ (v1_funct_1 @ X1)
% 0.49/0.67          | ~ (v1_relat_1 @ X0)
% 0.49/0.67          | ~ (v2_funct_1 @ X1))),
% 0.49/0.67      inference('sup+', [status(thm)], ['22', '33'])).
% 0.49/0.67  thf('35', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         (~ (v1_relat_1 @ X0)
% 0.49/0.67          | ~ (v2_funct_1 @ X1)
% 0.49/0.67          | ~ (v1_funct_1 @ X1)
% 0.49/0.67          | ~ (v1_relat_1 @ X1)
% 0.49/0.67          | (r1_tarski @ (k9_relat_1 @ X1 @ (k1_relat_1 @ X0)) @ 
% 0.49/0.67             (k9_relat_1 @ X1 @ (k1_relat_1 @ X0))))),
% 0.49/0.67      inference('simplify', [status(thm)], ['34'])).
% 0.49/0.67  thf('36', plain,
% 0.49/0.67      (![X0 : $i]:
% 0.49/0.67         ((r1_tarski @ (k2_relat_1 @ X0) @ 
% 0.49/0.67           (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.49/0.67          | ~ (v1_relat_1 @ X0)
% 0.49/0.67          | ~ (v1_relat_1 @ X0)
% 0.49/0.67          | ~ (v1_funct_1 @ X0)
% 0.49/0.67          | ~ (v2_funct_1 @ X0)
% 0.49/0.67          | ~ (v1_relat_1 @ X0))),
% 0.49/0.67      inference('sup+', [status(thm)], ['21', '35'])).
% 0.49/0.67  thf('37', plain,
% 0.49/0.67      (![X0 : $i]:
% 0.49/0.67         (~ (v2_funct_1 @ X0)
% 0.49/0.67          | ~ (v1_funct_1 @ X0)
% 0.49/0.67          | ~ (v1_relat_1 @ X0)
% 0.49/0.67          | (r1_tarski @ (k2_relat_1 @ X0) @ 
% 0.49/0.67             (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 0.49/0.67      inference('simplify', [status(thm)], ['36'])).
% 0.49/0.67  thf('38', plain,
% 0.49/0.67      (![X0 : $i]:
% 0.49/0.67         ((r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.49/0.67          | ~ (v1_relat_1 @ X0)
% 0.49/0.67          | ~ (v1_relat_1 @ X0)
% 0.49/0.67          | ~ (v1_funct_1 @ X0)
% 0.49/0.67          | ~ (v2_funct_1 @ X0))),
% 0.49/0.67      inference('sup+', [status(thm)], ['20', '37'])).
% 0.49/0.67  thf('39', plain,
% 0.49/0.67      (![X0 : $i]:
% 0.49/0.67         (~ (v2_funct_1 @ X0)
% 0.49/0.67          | ~ (v1_funct_1 @ X0)
% 0.49/0.67          | ~ (v1_relat_1 @ X0)
% 0.49/0.67          | (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.49/0.67      inference('simplify', [status(thm)], ['38'])).
% 0.49/0.67  thf('40', plain,
% 0.49/0.67      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.49/0.67         (~ (r1_tarski @ X7 @ X8)
% 0.49/0.67          | ~ (v1_relat_1 @ X9)
% 0.49/0.67          | (r1_tarski @ (k10_relat_1 @ X9 @ X7) @ (k10_relat_1 @ X9 @ X8)))),
% 0.49/0.67      inference('cnf', [status(esa)], [t178_relat_1])).
% 0.49/0.67  thf('41', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         (~ (v1_relat_1 @ X0)
% 0.49/0.67          | ~ (v1_funct_1 @ X0)
% 0.49/0.67          | ~ (v2_funct_1 @ X0)
% 0.49/0.67          | (r1_tarski @ (k10_relat_1 @ X1 @ (k2_relat_1 @ X0)) @ 
% 0.49/0.67             (k10_relat_1 @ X1 @ (k2_relat_1 @ X0)))
% 0.49/0.67          | ~ (v1_relat_1 @ X1))),
% 0.49/0.67      inference('sup-', [status(thm)], ['39', '40'])).
% 0.49/0.67  thf('42', plain,
% 0.49/0.67      (![X0 : $i]:
% 0.49/0.67         ((r1_tarski @ (k1_relat_1 @ X0) @ 
% 0.49/0.67           (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 0.49/0.67          | ~ (v1_relat_1 @ X0)
% 0.49/0.67          | ~ (v1_relat_1 @ X0)
% 0.49/0.67          | ~ (v2_funct_1 @ X0)
% 0.49/0.67          | ~ (v1_funct_1 @ X0)
% 0.49/0.67          | ~ (v1_relat_1 @ X0))),
% 0.49/0.67      inference('sup+', [status(thm)], ['19', '41'])).
% 0.49/0.67  thf('43', plain,
% 0.49/0.67      (![X0 : $i]:
% 0.49/0.67         (~ (v1_funct_1 @ X0)
% 0.49/0.67          | ~ (v2_funct_1 @ X0)
% 0.49/0.67          | ~ (v1_relat_1 @ X0)
% 0.49/0.67          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 0.49/0.67             (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 0.49/0.67      inference('simplify', [status(thm)], ['42'])).
% 0.49/0.67  thf(t164_funct_1, conjecture,
% 0.49/0.67    (![A:$i,B:$i]:
% 0.49/0.67     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.49/0.67       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.49/0.67         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.49/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.67    (~( ![A:$i,B:$i]:
% 0.49/0.67        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.49/0.67          ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.49/0.67            ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ) )),
% 0.49/0.67    inference('cnf.neg', [status(esa)], [t164_funct_1])).
% 0.49/0.67  thf('44', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf(t1_xboole_1, axiom,
% 0.49/0.67    (![A:$i,B:$i,C:$i]:
% 0.49/0.67     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.49/0.67       ( r1_tarski @ A @ C ) ))).
% 0.49/0.67  thf('45', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.67         (~ (r1_tarski @ X0 @ X1)
% 0.49/0.67          | ~ (r1_tarski @ X1 @ X2)
% 0.49/0.67          | (r1_tarski @ X0 @ X2))),
% 0.49/0.67      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.49/0.67  thf('46', plain,
% 0.49/0.67      (![X0 : $i]:
% 0.49/0.67         ((r1_tarski @ sk_A @ X0) | ~ (r1_tarski @ (k1_relat_1 @ sk_B) @ X0))),
% 0.49/0.67      inference('sup-', [status(thm)], ['44', '45'])).
% 0.49/0.67  thf('47', plain,
% 0.49/0.67      ((~ (v1_relat_1 @ sk_B)
% 0.49/0.67        | ~ (v2_funct_1 @ sk_B)
% 0.49/0.67        | ~ (v1_funct_1 @ sk_B)
% 0.49/0.67        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))))),
% 0.49/0.67      inference('sup-', [status(thm)], ['43', '46'])).
% 0.49/0.67  thf('48', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('49', plain, ((v2_funct_1 @ sk_B)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('50', plain, ((v1_funct_1 @ sk_B)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('51', plain,
% 0.49/0.67      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 0.49/0.67      inference('demod', [status(thm)], ['47', '48', '49', '50'])).
% 0.49/0.67  thf('52', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.67         (~ (r1_tarski @ X0 @ X1)
% 0.49/0.67          | ~ (r1_tarski @ X1 @ X2)
% 0.49/0.67          | (r1_tarski @ X0 @ X2))),
% 0.49/0.67      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.49/0.67  thf('53', plain,
% 0.49/0.67      (![X0 : $i]:
% 0.49/0.67         ((r1_tarski @ sk_A @ X0)
% 0.49/0.67          | ~ (r1_tarski @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)) @ X0))),
% 0.49/0.67      inference('sup-', [status(thm)], ['51', '52'])).
% 0.49/0.67  thf('54', plain,
% 0.49/0.67      ((~ (v1_relat_1 @ sk_B)
% 0.49/0.67        | ~ (v2_funct_1 @ sk_B)
% 0.49/0.67        | ~ (v1_funct_1 @ sk_B)
% 0.49/0.67        | ~ (v1_relat_1 @ sk_B)
% 0.49/0.67        | (r1_tarski @ sk_A @ 
% 0.49/0.67           (k10_relat_1 @ sk_B @ (k1_relat_1 @ (k2_funct_1 @ sk_B)))))),
% 0.49/0.67      inference('sup-', [status(thm)], ['18', '53'])).
% 0.49/0.67  thf('55', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('56', plain, ((v2_funct_1 @ sk_B)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('57', plain, ((v1_funct_1 @ sk_B)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('58', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('59', plain,
% 0.49/0.67      ((r1_tarski @ sk_A @ 
% 0.49/0.67        (k10_relat_1 @ sk_B @ (k1_relat_1 @ (k2_funct_1 @ sk_B))))),
% 0.49/0.67      inference('demod', [status(thm)], ['54', '55', '56', '57', '58'])).
% 0.49/0.67  thf('60', plain,
% 0.49/0.67      (((r1_tarski @ sk_A @ (k2_relat_1 @ (k2_funct_1 @ sk_B)))
% 0.49/0.67        | ~ (v1_relat_1 @ sk_B)
% 0.49/0.67        | ~ (v1_funct_1 @ sk_B)
% 0.49/0.67        | ~ (v2_funct_1 @ sk_B))),
% 0.49/0.67      inference('sup+', [status(thm)], ['7', '59'])).
% 0.49/0.67  thf('61', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('62', plain, ((v1_funct_1 @ sk_B)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('63', plain, ((v2_funct_1 @ sk_B)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('64', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ (k2_funct_1 @ sk_B)))),
% 0.49/0.67      inference('demod', [status(thm)], ['60', '61', '62', '63'])).
% 0.49/0.67  thf(t147_funct_1, axiom,
% 0.49/0.67    (![A:$i,B:$i]:
% 0.49/0.67     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.49/0.67       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.49/0.67         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.49/0.67  thf('65', plain,
% 0.49/0.67      (![X11 : $i, X12 : $i]:
% 0.49/0.67         (~ (r1_tarski @ X11 @ (k2_relat_1 @ X12))
% 0.49/0.67          | ((k9_relat_1 @ X12 @ (k10_relat_1 @ X12 @ X11)) = (X11))
% 0.49/0.67          | ~ (v1_funct_1 @ X12)
% 0.49/0.67          | ~ (v1_relat_1 @ X12))),
% 0.49/0.67      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.49/0.67  thf('66', plain,
% 0.49/0.67      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.49/0.67        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.49/0.67        | ((k9_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 0.49/0.67            (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)) = (sk_A)))),
% 0.49/0.67      inference('sup-', [status(thm)], ['64', '65'])).
% 0.49/0.67  thf('67', plain,
% 0.49/0.67      (![X13 : $i, X14 : $i]:
% 0.49/0.67         (~ (v2_funct_1 @ X13)
% 0.49/0.67          | ((k9_relat_1 @ X13 @ X14)
% 0.49/0.67              = (k10_relat_1 @ (k2_funct_1 @ X13) @ X14))
% 0.49/0.67          | ~ (v1_funct_1 @ X13)
% 0.49/0.67          | ~ (v1_relat_1 @ X13))),
% 0.49/0.67      inference('cnf', [status(esa)], [t154_funct_1])).
% 0.49/0.67  thf('68', plain,
% 0.49/0.67      (![X3 : $i]:
% 0.49/0.67         (((k9_relat_1 @ X3 @ (k1_relat_1 @ X3)) = (k2_relat_1 @ X3))
% 0.49/0.67          | ~ (v1_relat_1 @ X3))),
% 0.49/0.67      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.49/0.67  thf('69', plain,
% 0.49/0.67      (![X10 : $i]:
% 0.49/0.67         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 0.49/0.67          | ~ (v1_funct_1 @ X10)
% 0.49/0.67          | ~ (v1_relat_1 @ X10))),
% 0.49/0.67      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.49/0.67  thf('70', plain,
% 0.49/0.67      (![X13 : $i, X14 : $i]:
% 0.49/0.67         (~ (v2_funct_1 @ X13)
% 0.49/0.67          | ((k9_relat_1 @ X13 @ X14)
% 0.49/0.67              = (k10_relat_1 @ (k2_funct_1 @ X13) @ X14))
% 0.49/0.67          | ~ (v1_funct_1 @ X13)
% 0.49/0.67          | ~ (v1_relat_1 @ X13))),
% 0.49/0.67      inference('cnf', [status(esa)], [t154_funct_1])).
% 0.49/0.67  thf('71', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('72', plain,
% 0.49/0.67      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.49/0.67         (~ (r1_tarski @ X7 @ X8)
% 0.49/0.67          | ~ (v1_relat_1 @ X9)
% 0.49/0.67          | (r1_tarski @ (k10_relat_1 @ X9 @ X7) @ (k10_relat_1 @ X9 @ X8)))),
% 0.49/0.67      inference('cnf', [status(esa)], [t178_relat_1])).
% 0.49/0.67  thf('73', plain,
% 0.49/0.67      (![X0 : $i]:
% 0.49/0.67         ((r1_tarski @ (k10_relat_1 @ X0 @ sk_A) @ 
% 0.49/0.67           (k10_relat_1 @ X0 @ (k1_relat_1 @ sk_B)))
% 0.49/0.67          | ~ (v1_relat_1 @ X0))),
% 0.49/0.67      inference('sup-', [status(thm)], ['71', '72'])).
% 0.49/0.67  thf('74', plain,
% 0.49/0.67      (![X0 : $i]:
% 0.49/0.67         ((r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ X0) @ sk_A) @ 
% 0.49/0.67           (k9_relat_1 @ X0 @ (k1_relat_1 @ sk_B)))
% 0.49/0.67          | ~ (v1_relat_1 @ X0)
% 0.49/0.67          | ~ (v1_funct_1 @ X0)
% 0.49/0.67          | ~ (v2_funct_1 @ X0)
% 0.49/0.67          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.49/0.67      inference('sup+', [status(thm)], ['70', '73'])).
% 0.49/0.67  thf('75', plain,
% 0.49/0.67      (![X0 : $i]:
% 0.49/0.67         (~ (v1_relat_1 @ X0)
% 0.49/0.67          | ~ (v1_funct_1 @ X0)
% 0.49/0.67          | ~ (v2_funct_1 @ X0)
% 0.49/0.67          | ~ (v1_funct_1 @ X0)
% 0.49/0.67          | ~ (v1_relat_1 @ X0)
% 0.49/0.67          | (r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ X0) @ sk_A) @ 
% 0.49/0.67             (k9_relat_1 @ X0 @ (k1_relat_1 @ sk_B))))),
% 0.49/0.67      inference('sup-', [status(thm)], ['69', '74'])).
% 0.49/0.67  thf('76', plain,
% 0.49/0.67      (![X0 : $i]:
% 0.49/0.67         ((r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ X0) @ sk_A) @ 
% 0.49/0.67           (k9_relat_1 @ X0 @ (k1_relat_1 @ sk_B)))
% 0.49/0.67          | ~ (v2_funct_1 @ X0)
% 0.49/0.67          | ~ (v1_funct_1 @ X0)
% 0.49/0.67          | ~ (v1_relat_1 @ X0))),
% 0.49/0.67      inference('simplify', [status(thm)], ['75'])).
% 0.49/0.67  thf('77', plain,
% 0.49/0.67      (((r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A) @ 
% 0.49/0.67         (k2_relat_1 @ sk_B))
% 0.49/0.67        | ~ (v1_relat_1 @ sk_B)
% 0.49/0.67        | ~ (v1_relat_1 @ sk_B)
% 0.49/0.67        | ~ (v1_funct_1 @ sk_B)
% 0.49/0.67        | ~ (v2_funct_1 @ sk_B))),
% 0.49/0.67      inference('sup+', [status(thm)], ['68', '76'])).
% 0.49/0.67  thf('78', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('79', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('80', plain, ((v1_funct_1 @ sk_B)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('81', plain, ((v2_funct_1 @ sk_B)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('82', plain,
% 0.49/0.67      ((r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A) @ 
% 0.49/0.67        (k2_relat_1 @ sk_B))),
% 0.49/0.67      inference('demod', [status(thm)], ['77', '78', '79', '80', '81'])).
% 0.49/0.67  thf('83', plain,
% 0.49/0.67      (![X11 : $i, X12 : $i]:
% 0.49/0.67         (~ (r1_tarski @ X11 @ (k2_relat_1 @ X12))
% 0.49/0.67          | ((k9_relat_1 @ X12 @ (k10_relat_1 @ X12 @ X11)) = (X11))
% 0.49/0.67          | ~ (v1_funct_1 @ X12)
% 0.49/0.67          | ~ (v1_relat_1 @ X12))),
% 0.49/0.67      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.49/0.67  thf('84', plain,
% 0.49/0.67      ((~ (v1_relat_1 @ sk_B)
% 0.49/0.67        | ~ (v1_funct_1 @ sk_B)
% 0.49/0.67        | ((k9_relat_1 @ sk_B @ 
% 0.49/0.67            (k10_relat_1 @ sk_B @ (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)))
% 0.49/0.67            = (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)))),
% 0.49/0.67      inference('sup-', [status(thm)], ['82', '83'])).
% 0.49/0.67  thf('85', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('86', plain, ((v1_funct_1 @ sk_B)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('87', plain,
% 0.49/0.67      (((k9_relat_1 @ sk_B @ 
% 0.49/0.67         (k10_relat_1 @ sk_B @ (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)))
% 0.49/0.67         = (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A))),
% 0.49/0.67      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.49/0.67  thf('88', plain,
% 0.49/0.67      ((((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.49/0.67          = (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A))
% 0.49/0.67        | ~ (v1_relat_1 @ sk_B)
% 0.49/0.67        | ~ (v1_funct_1 @ sk_B)
% 0.49/0.67        | ~ (v2_funct_1 @ sk_B))),
% 0.49/0.67      inference('sup+', [status(thm)], ['67', '87'])).
% 0.49/0.67  thf('89', plain,
% 0.49/0.67      (![X13 : $i, X14 : $i]:
% 0.49/0.67         (~ (v2_funct_1 @ X13)
% 0.49/0.67          | ((k9_relat_1 @ X13 @ X14)
% 0.49/0.67              = (k10_relat_1 @ (k2_funct_1 @ X13) @ X14))
% 0.49/0.67          | ~ (v1_funct_1 @ X13)
% 0.49/0.67          | ~ (v1_relat_1 @ X13))),
% 0.49/0.67      inference('cnf', [status(esa)], [t154_funct_1])).
% 0.49/0.67  thf('90', plain,
% 0.49/0.67      ((r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A) @ 
% 0.49/0.67        (k2_relat_1 @ sk_B))),
% 0.49/0.67      inference('demod', [status(thm)], ['77', '78', '79', '80', '81'])).
% 0.49/0.67  thf('91', plain,
% 0.49/0.67      (((r1_tarski @ (k9_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))
% 0.49/0.67        | ~ (v1_relat_1 @ sk_B)
% 0.49/0.67        | ~ (v1_funct_1 @ sk_B)
% 0.49/0.67        | ~ (v2_funct_1 @ sk_B))),
% 0.49/0.67      inference('sup+', [status(thm)], ['89', '90'])).
% 0.49/0.67  thf('92', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('93', plain, ((v1_funct_1 @ sk_B)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('94', plain, ((v2_funct_1 @ sk_B)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('95', plain,
% 0.49/0.67      ((r1_tarski @ (k9_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))),
% 0.49/0.67      inference('demod', [status(thm)], ['91', '92', '93', '94'])).
% 0.49/0.67  thf('96', plain,
% 0.49/0.67      (![X11 : $i, X12 : $i]:
% 0.49/0.67         (~ (r1_tarski @ X11 @ (k2_relat_1 @ X12))
% 0.49/0.67          | ((k9_relat_1 @ X12 @ (k10_relat_1 @ X12 @ X11)) = (X11))
% 0.49/0.67          | ~ (v1_funct_1 @ X12)
% 0.49/0.67          | ~ (v1_relat_1 @ X12))),
% 0.49/0.67      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.49/0.67  thf('97', plain,
% 0.49/0.67      ((~ (v1_relat_1 @ sk_B)
% 0.49/0.67        | ~ (v1_funct_1 @ sk_B)
% 0.49/0.67        | ((k9_relat_1 @ sk_B @ 
% 0.49/0.67            (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.49/0.67            = (k9_relat_1 @ sk_B @ sk_A)))),
% 0.49/0.67      inference('sup-', [status(thm)], ['95', '96'])).
% 0.49/0.67  thf('98', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('99', plain, ((v1_funct_1 @ sk_B)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('100', plain,
% 0.49/0.67      (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.49/0.67         = (k9_relat_1 @ sk_B @ sk_A))),
% 0.49/0.67      inference('demod', [status(thm)], ['97', '98', '99'])).
% 0.49/0.67  thf('101', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('102', plain, ((v1_funct_1 @ sk_B)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('103', plain, ((v2_funct_1 @ sk_B)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('104', plain,
% 0.49/0.67      (((k9_relat_1 @ sk_B @ sk_A) = (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A))),
% 0.49/0.67      inference('demod', [status(thm)], ['88', '100', '101', '102', '103'])).
% 0.49/0.67  thf('105', plain,
% 0.49/0.67      (![X10 : $i]:
% 0.49/0.67         ((v1_funct_1 @ (k2_funct_1 @ X10))
% 0.49/0.67          | ~ (v1_funct_1 @ X10)
% 0.49/0.67          | ~ (v1_relat_1 @ X10))),
% 0.49/0.67      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.49/0.68  thf('106', plain,
% 0.49/0.68      (![X10 : $i]:
% 0.49/0.68         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 0.49/0.68          | ~ (v1_funct_1 @ X10)
% 0.49/0.68          | ~ (v1_relat_1 @ X10))),
% 0.49/0.68      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.49/0.68  thf('107', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         (((k10_relat_1 @ X0 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.49/0.68            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.49/0.68          | ~ (v2_funct_1 @ X0)
% 0.49/0.68          | ~ (v1_funct_1 @ X0)
% 0.49/0.68          | ~ (v1_relat_1 @ X0))),
% 0.49/0.68      inference('simplify', [status(thm)], ['6'])).
% 0.49/0.68  thf('108', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         (~ (v2_funct_1 @ X0)
% 0.49/0.68          | ~ (v1_funct_1 @ X0)
% 0.49/0.68          | ~ (v1_relat_1 @ X0)
% 0.49/0.68          | (r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 0.49/0.68      inference('simplify', [status(thm)], ['15'])).
% 0.49/0.68  thf('109', plain,
% 0.49/0.68      ((r1_tarski @ (k9_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))),
% 0.49/0.68      inference('demod', [status(thm)], ['91', '92', '93', '94'])).
% 0.49/0.68  thf('110', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.68         (~ (r1_tarski @ X0 @ X1)
% 0.49/0.68          | ~ (r1_tarski @ X1 @ X2)
% 0.49/0.68          | (r1_tarski @ X0 @ X2))),
% 0.49/0.68      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.49/0.68  thf('111', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         ((r1_tarski @ (k9_relat_1 @ sk_B @ sk_A) @ X0)
% 0.49/0.68          | ~ (r1_tarski @ (k2_relat_1 @ sk_B) @ X0))),
% 0.49/0.68      inference('sup-', [status(thm)], ['109', '110'])).
% 0.49/0.68  thf('112', plain,
% 0.49/0.68      ((~ (v1_relat_1 @ sk_B)
% 0.49/0.68        | ~ (v1_funct_1 @ sk_B)
% 0.49/0.68        | ~ (v2_funct_1 @ sk_B)
% 0.49/0.68        | (r1_tarski @ (k9_relat_1 @ sk_B @ sk_A) @ 
% 0.49/0.68           (k1_relat_1 @ (k2_funct_1 @ sk_B))))),
% 0.49/0.68      inference('sup-', [status(thm)], ['108', '111'])).
% 0.49/0.68  thf('113', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('114', plain, ((v1_funct_1 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('115', plain, ((v2_funct_1 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('116', plain,
% 0.49/0.68      ((r1_tarski @ (k9_relat_1 @ sk_B @ sk_A) @ 
% 0.49/0.68        (k1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 0.49/0.68      inference('demod', [status(thm)], ['112', '113', '114', '115'])).
% 0.49/0.68  thf('117', plain,
% 0.49/0.68      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.49/0.68         (~ (r1_tarski @ X7 @ X8)
% 0.49/0.68          | ~ (v1_relat_1 @ X9)
% 0.49/0.68          | (r1_tarski @ (k10_relat_1 @ X9 @ X7) @ (k10_relat_1 @ X9 @ X8)))),
% 0.49/0.68      inference('cnf', [status(esa)], [t178_relat_1])).
% 0.49/0.68  thf('118', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         ((r1_tarski @ (k10_relat_1 @ X0 @ (k9_relat_1 @ sk_B @ sk_A)) @ 
% 0.49/0.68           (k10_relat_1 @ X0 @ (k1_relat_1 @ (k2_funct_1 @ sk_B))))
% 0.49/0.68          | ~ (v1_relat_1 @ X0))),
% 0.49/0.68      inference('sup-', [status(thm)], ['116', '117'])).
% 0.49/0.68  thf('119', plain,
% 0.49/0.68      (((r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ 
% 0.49/0.68         (k2_relat_1 @ (k2_funct_1 @ sk_B)))
% 0.49/0.68        | ~ (v1_relat_1 @ sk_B)
% 0.49/0.68        | ~ (v1_funct_1 @ sk_B)
% 0.49/0.68        | ~ (v2_funct_1 @ sk_B)
% 0.49/0.68        | ~ (v1_relat_1 @ sk_B))),
% 0.49/0.68      inference('sup+', [status(thm)], ['107', '118'])).
% 0.49/0.68  thf('120', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('121', plain, ((v1_funct_1 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('122', plain, ((v2_funct_1 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('123', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('124', plain,
% 0.49/0.68      ((r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ 
% 0.49/0.68        (k2_relat_1 @ (k2_funct_1 @ sk_B)))),
% 0.49/0.68      inference('demod', [status(thm)], ['119', '120', '121', '122', '123'])).
% 0.49/0.68  thf('125', plain,
% 0.49/0.68      (![X11 : $i, X12 : $i]:
% 0.49/0.68         (~ (r1_tarski @ X11 @ (k2_relat_1 @ X12))
% 0.49/0.68          | ((k9_relat_1 @ X12 @ (k10_relat_1 @ X12 @ X11)) = (X11))
% 0.49/0.68          | ~ (v1_funct_1 @ X12)
% 0.49/0.68          | ~ (v1_relat_1 @ X12))),
% 0.49/0.68      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.49/0.68  thf('126', plain,
% 0.49/0.68      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.49/0.68        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.49/0.68        | ((k9_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 0.49/0.68            (k10_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 0.49/0.68             (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))
% 0.49/0.68            = (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 0.49/0.68      inference('sup-', [status(thm)], ['124', '125'])).
% 0.49/0.68  thf('127', plain,
% 0.49/0.68      (![X13 : $i, X14 : $i]:
% 0.49/0.68         (~ (v2_funct_1 @ X13)
% 0.49/0.68          | ((k9_relat_1 @ X13 @ X14)
% 0.49/0.68              = (k10_relat_1 @ (k2_funct_1 @ X13) @ X14))
% 0.49/0.68          | ~ (v1_funct_1 @ X13)
% 0.49/0.68          | ~ (v1_relat_1 @ X13))),
% 0.49/0.68      inference('cnf', [status(esa)], [t154_funct_1])).
% 0.49/0.68  thf('128', plain,
% 0.49/0.68      (![X10 : $i]:
% 0.49/0.68         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 0.49/0.68          | ~ (v1_funct_1 @ X10)
% 0.49/0.68          | ~ (v1_relat_1 @ X10))),
% 0.49/0.68      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.49/0.68  thf('129', plain,
% 0.49/0.68      (![X3 : $i]:
% 0.49/0.68         (((k9_relat_1 @ X3 @ (k1_relat_1 @ X3)) = (k2_relat_1 @ X3))
% 0.49/0.68          | ~ (v1_relat_1 @ X3))),
% 0.49/0.68      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.49/0.68  thf('130', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         ((r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X1)) @ 
% 0.49/0.68           (k9_relat_1 @ X0 @ (k1_relat_1 @ X1)))
% 0.49/0.68          | ~ (v2_funct_1 @ X0)
% 0.49/0.68          | ~ (v1_relat_1 @ X1)
% 0.49/0.68          | ~ (v1_funct_1 @ X0)
% 0.49/0.68          | ~ (v1_relat_1 @ X0))),
% 0.49/0.68      inference('simplify', [status(thm)], ['32'])).
% 0.49/0.68  thf('131', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         ((r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0)) @ 
% 0.49/0.68           (k2_relat_1 @ X0))
% 0.49/0.68          | ~ (v1_relat_1 @ X0)
% 0.49/0.68          | ~ (v1_relat_1 @ X0)
% 0.49/0.68          | ~ (v1_funct_1 @ X0)
% 0.49/0.68          | ~ (v1_relat_1 @ X0)
% 0.49/0.68          | ~ (v2_funct_1 @ X0))),
% 0.49/0.68      inference('sup+', [status(thm)], ['129', '130'])).
% 0.49/0.68  thf('132', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         (~ (v2_funct_1 @ X0)
% 0.49/0.68          | ~ (v1_funct_1 @ X0)
% 0.49/0.68          | ~ (v1_relat_1 @ X0)
% 0.49/0.68          | (r1_tarski @ 
% 0.49/0.68             (k10_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0)) @ 
% 0.49/0.68             (k2_relat_1 @ X0)))),
% 0.49/0.68      inference('simplify', [status(thm)], ['131'])).
% 0.49/0.68  thf('133', plain,
% 0.49/0.68      (![X6 : $i]:
% 0.49/0.68         (((k10_relat_1 @ X6 @ (k2_relat_1 @ X6)) = (k1_relat_1 @ X6))
% 0.49/0.68          | ~ (v1_relat_1 @ X6))),
% 0.49/0.68      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.49/0.68  thf('134', plain,
% 0.49/0.68      ((r1_tarski @ (k9_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))),
% 0.49/0.68      inference('demod', [status(thm)], ['91', '92', '93', '94'])).
% 0.49/0.68  thf('135', plain,
% 0.49/0.68      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.49/0.68         (~ (r1_tarski @ X7 @ X8)
% 0.49/0.68          | ~ (v1_relat_1 @ X9)
% 0.49/0.68          | (r1_tarski @ (k10_relat_1 @ X9 @ X7) @ (k10_relat_1 @ X9 @ X8)))),
% 0.49/0.68      inference('cnf', [status(esa)], [t178_relat_1])).
% 0.49/0.68  thf('136', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         ((r1_tarski @ (k10_relat_1 @ X0 @ (k9_relat_1 @ sk_B @ sk_A)) @ 
% 0.49/0.68           (k10_relat_1 @ X0 @ (k2_relat_1 @ sk_B)))
% 0.49/0.68          | ~ (v1_relat_1 @ X0))),
% 0.49/0.68      inference('sup-', [status(thm)], ['134', '135'])).
% 0.49/0.68  thf('137', plain,
% 0.49/0.68      (((r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ 
% 0.49/0.68         (k1_relat_1 @ sk_B))
% 0.49/0.68        | ~ (v1_relat_1 @ sk_B)
% 0.49/0.68        | ~ (v1_relat_1 @ sk_B))),
% 0.49/0.68      inference('sup+', [status(thm)], ['133', '136'])).
% 0.49/0.68  thf('138', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('139', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('140', plain,
% 0.49/0.68      ((r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ 
% 0.49/0.68        (k1_relat_1 @ sk_B))),
% 0.49/0.68      inference('demod', [status(thm)], ['137', '138', '139'])).
% 0.49/0.68  thf('141', plain,
% 0.49/0.68      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.49/0.68         (~ (r1_tarski @ X7 @ X8)
% 0.49/0.68          | ~ (v1_relat_1 @ X9)
% 0.49/0.68          | (r1_tarski @ (k10_relat_1 @ X9 @ X7) @ (k10_relat_1 @ X9 @ X8)))),
% 0.49/0.68      inference('cnf', [status(esa)], [t178_relat_1])).
% 0.49/0.68  thf('142', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         ((r1_tarski @ 
% 0.49/0.68           (k10_relat_1 @ X0 @ 
% 0.49/0.68            (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))) @ 
% 0.49/0.68           (k10_relat_1 @ X0 @ (k1_relat_1 @ sk_B)))
% 0.49/0.68          | ~ (v1_relat_1 @ X0))),
% 0.49/0.68      inference('sup-', [status(thm)], ['140', '141'])).
% 0.49/0.68  thf('143', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.68         (~ (r1_tarski @ X0 @ X1)
% 0.49/0.68          | ~ (r1_tarski @ X1 @ X2)
% 0.49/0.68          | (r1_tarski @ X0 @ X2))),
% 0.49/0.68      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.49/0.68  thf('144', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (~ (v1_relat_1 @ X0)
% 0.49/0.68          | (r1_tarski @ 
% 0.49/0.68             (k10_relat_1 @ X0 @ 
% 0.49/0.68              (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))) @ 
% 0.49/0.68             X1)
% 0.49/0.68          | ~ (r1_tarski @ (k10_relat_1 @ X0 @ (k1_relat_1 @ sk_B)) @ X1))),
% 0.49/0.68      inference('sup-', [status(thm)], ['142', '143'])).
% 0.49/0.68  thf('145', plain,
% 0.49/0.68      ((~ (v1_relat_1 @ sk_B)
% 0.49/0.68        | ~ (v1_funct_1 @ sk_B)
% 0.49/0.68        | ~ (v2_funct_1 @ sk_B)
% 0.49/0.68        | (r1_tarski @ 
% 0.49/0.68           (k10_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 0.49/0.68            (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))) @ 
% 0.49/0.68           (k2_relat_1 @ sk_B))
% 0.49/0.68        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['132', '144'])).
% 0.49/0.68  thf('146', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('147', plain, ((v1_funct_1 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('148', plain, ((v2_funct_1 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('149', plain,
% 0.49/0.68      (((r1_tarski @ 
% 0.49/0.68         (k10_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 0.49/0.68          (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))) @ 
% 0.49/0.68         (k2_relat_1 @ sk_B))
% 0.49/0.68        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 0.49/0.68      inference('demod', [status(thm)], ['145', '146', '147', '148'])).
% 0.49/0.68  thf('150', plain,
% 0.49/0.68      ((~ (v1_relat_1 @ sk_B)
% 0.49/0.68        | ~ (v1_funct_1 @ sk_B)
% 0.49/0.68        | (r1_tarski @ 
% 0.49/0.68           (k10_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 0.49/0.68            (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))) @ 
% 0.49/0.68           (k2_relat_1 @ sk_B)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['128', '149'])).
% 0.49/0.68  thf('151', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('152', plain, ((v1_funct_1 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('153', plain,
% 0.49/0.68      ((r1_tarski @ 
% 0.49/0.68        (k10_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 0.49/0.68         (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))) @ 
% 0.49/0.68        (k2_relat_1 @ sk_B))),
% 0.49/0.68      inference('demod', [status(thm)], ['150', '151', '152'])).
% 0.49/0.68  thf('154', plain,
% 0.49/0.68      (![X11 : $i, X12 : $i]:
% 0.49/0.68         (~ (r1_tarski @ X11 @ (k2_relat_1 @ X12))
% 0.49/0.68          | ((k9_relat_1 @ X12 @ (k10_relat_1 @ X12 @ X11)) = (X11))
% 0.49/0.68          | ~ (v1_funct_1 @ X12)
% 0.49/0.68          | ~ (v1_relat_1 @ X12))),
% 0.49/0.68      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.49/0.68  thf('155', plain,
% 0.49/0.68      ((~ (v1_relat_1 @ sk_B)
% 0.49/0.68        | ~ (v1_funct_1 @ sk_B)
% 0.49/0.68        | ((k9_relat_1 @ sk_B @ 
% 0.49/0.68            (k10_relat_1 @ sk_B @ 
% 0.49/0.68             (k10_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 0.49/0.68              (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))))
% 0.49/0.68            = (k10_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 0.49/0.68               (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))))),
% 0.49/0.68      inference('sup-', [status(thm)], ['153', '154'])).
% 0.49/0.68  thf('156', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('157', plain, ((v1_funct_1 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('158', plain,
% 0.49/0.68      (((k9_relat_1 @ sk_B @ 
% 0.49/0.68         (k10_relat_1 @ sk_B @ 
% 0.49/0.68          (k10_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 0.49/0.68           (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))))
% 0.49/0.68         = (k10_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 0.49/0.68            (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 0.49/0.68      inference('demod', [status(thm)], ['155', '156', '157'])).
% 0.49/0.68  thf('159', plain,
% 0.49/0.68      ((((k9_relat_1 @ sk_B @ 
% 0.49/0.68          (k10_relat_1 @ sk_B @ 
% 0.49/0.68           (k9_relat_1 @ sk_B @ 
% 0.49/0.68            (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))))
% 0.49/0.68          = (k10_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 0.49/0.68             (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))
% 0.49/0.68        | ~ (v1_relat_1 @ sk_B)
% 0.49/0.68        | ~ (v1_funct_1 @ sk_B)
% 0.49/0.68        | ~ (v2_funct_1 @ sk_B))),
% 0.49/0.68      inference('sup+', [status(thm)], ['127', '158'])).
% 0.49/0.68  thf('160', plain,
% 0.49/0.68      (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.49/0.68         = (k9_relat_1 @ sk_B @ sk_A))),
% 0.49/0.68      inference('demod', [status(thm)], ['97', '98', '99'])).
% 0.49/0.68  thf('161', plain,
% 0.49/0.68      (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.49/0.68         = (k9_relat_1 @ sk_B @ sk_A))),
% 0.49/0.68      inference('demod', [status(thm)], ['97', '98', '99'])).
% 0.49/0.68  thf('162', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('163', plain, ((v1_funct_1 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('164', plain, ((v2_funct_1 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('165', plain,
% 0.49/0.68      (((k9_relat_1 @ sk_B @ sk_A)
% 0.49/0.68         = (k10_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 0.49/0.68            (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 0.49/0.68      inference('demod', [status(thm)],
% 0.49/0.68                ['159', '160', '161', '162', '163', '164'])).
% 0.49/0.68  thf('166', plain,
% 0.49/0.68      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.49/0.68        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.49/0.68        | ((k9_relat_1 @ (k2_funct_1 @ sk_B) @ (k9_relat_1 @ sk_B @ sk_A))
% 0.49/0.68            = (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 0.49/0.68      inference('demod', [status(thm)], ['126', '165'])).
% 0.49/0.68  thf('167', plain,
% 0.49/0.68      ((~ (v1_relat_1 @ sk_B)
% 0.49/0.68        | ~ (v1_funct_1 @ sk_B)
% 0.49/0.68        | ((k9_relat_1 @ (k2_funct_1 @ sk_B) @ (k9_relat_1 @ sk_B @ sk_A))
% 0.49/0.68            = (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.49/0.68        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['106', '166'])).
% 0.49/0.68  thf('168', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('169', plain, ((v1_funct_1 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('170', plain,
% 0.49/0.68      ((((k9_relat_1 @ (k2_funct_1 @ sk_B) @ (k9_relat_1 @ sk_B @ sk_A))
% 0.49/0.68          = (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.49/0.68        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.49/0.68      inference('demod', [status(thm)], ['167', '168', '169'])).
% 0.49/0.68  thf('171', plain,
% 0.49/0.68      ((~ (v1_relat_1 @ sk_B)
% 0.49/0.68        | ~ (v1_funct_1 @ sk_B)
% 0.49/0.68        | ((k9_relat_1 @ (k2_funct_1 @ sk_B) @ (k9_relat_1 @ sk_B @ sk_A))
% 0.49/0.68            = (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 0.49/0.68      inference('sup-', [status(thm)], ['105', '170'])).
% 0.49/0.68  thf('172', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('173', plain, ((v1_funct_1 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('174', plain,
% 0.49/0.68      (((k9_relat_1 @ (k2_funct_1 @ sk_B) @ (k9_relat_1 @ sk_B @ sk_A))
% 0.49/0.68         = (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.49/0.68      inference('demod', [status(thm)], ['171', '172', '173'])).
% 0.49/0.68  thf('175', plain,
% 0.49/0.68      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.49/0.68        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.49/0.68        | ((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) = (sk_A)))),
% 0.49/0.68      inference('demod', [status(thm)], ['66', '104', '174'])).
% 0.49/0.68  thf('176', plain,
% 0.49/0.68      (((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) != (sk_A))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('177', plain,
% 0.49/0.68      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.49/0.68        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.49/0.68      inference('simplify_reflect-', [status(thm)], ['175', '176'])).
% 0.49/0.68  thf('178', plain,
% 0.49/0.68      ((~ (v1_relat_1 @ sk_B)
% 0.49/0.68        | ~ (v1_funct_1 @ sk_B)
% 0.49/0.68        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['1', '177'])).
% 0.49/0.68  thf('179', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('180', plain, ((v1_funct_1 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('181', plain, (~ (v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.49/0.68      inference('demod', [status(thm)], ['178', '179', '180'])).
% 0.49/0.68  thf('182', plain, ((~ (v1_relat_1 @ sk_B) | ~ (v1_funct_1 @ sk_B))),
% 0.49/0.68      inference('sup-', [status(thm)], ['0', '181'])).
% 0.49/0.68  thf('183', plain, ((v1_relat_1 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('184', plain, ((v1_funct_1 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('185', plain, ($false),
% 0.49/0.68      inference('demod', [status(thm)], ['182', '183', '184'])).
% 0.49/0.68  
% 0.49/0.68  % SZS output end Refutation
% 0.49/0.68  
% 0.49/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
