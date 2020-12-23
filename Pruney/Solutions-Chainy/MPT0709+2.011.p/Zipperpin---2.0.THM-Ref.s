%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xvYjyAuf8H

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:07 EST 2020

% Result     : Theorem 0.99s
% Output     : Refutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 492 expanded)
%              Number of leaves         :   35 ( 167 expanded)
%              Depth                    :   30
%              Number of atoms          : 1433 (4456 expanded)
%              Number of equality atoms :   89 ( 354 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

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

thf('0',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( r1_tarski @ X44 @ ( k1_relat_1 @ X45 ) )
      | ( r1_tarski @ X44 @ ( k10_relat_1 @ X45 @ ( k9_relat_1 @ X45 @ X44 ) ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('2',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,
    ( ~ ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ sk_A )
    | ( ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k6_subset_1 @ X30 @ X31 )
      = ( k4_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('13',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k6_subset_1 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf(t138_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('15',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( ( k10_relat_1 @ X39 @ ( k6_subset_1 @ X40 @ X41 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X39 @ X40 ) @ ( k10_relat_1 @ X39 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ ( k6_subset_1 @ X0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('18',plain,(
    ! [X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('19',plain,(
    ! [X42: $i,X43: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X42 @ ( k10_relat_1 @ X42 @ X43 ) ) @ X43 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('22',plain,(
    ! [X14: $i] :
      ( r1_tarski @ k1_xboole_0 @ X14 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('23',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k6_subset_1 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('28',plain,
    ( ( k6_subset_1 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('29',plain,(
    ! [X34: $i] :
      ( ( ( k9_relat_1 @ X34 @ ( k1_relat_1 @ X34 ) )
        = ( k2_relat_1 @ X34 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t123_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( v2_funct_1 @ C )
       => ( ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
          = ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ) )).

thf('30',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( v2_funct_1 @ X36 )
      | ( ( k9_relat_1 @ X36 @ ( k6_subset_1 @ X37 @ X38 ) )
        = ( k6_subset_1 @ ( k9_relat_1 @ X36 @ X37 ) @ ( k9_relat_1 @ X36 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t123_funct_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k6_subset_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k6_subset_1 @ ( k9_relat_1 @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k6_subset_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k6_subset_1 @ ( k9_relat_1 @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( ( k9_relat_1 @ sk_B @ k1_xboole_0 )
      = ( k6_subset_1 @ ( k9_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['28','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k9_relat_1 @ sk_B @ k1_xboole_0 )
    = ( k6_subset_1 @ ( k9_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34','35','36'])).

thf('38',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('39',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k6_subset_1 @ X30 @ X31 )
      = ( k4_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('40',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k6_subset_1 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k9_relat_1 @ sk_B @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( r1_tarski @ ( k9_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r1_tarski @ ( k9_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k9_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k6_subset_1 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('48',plain,
    ( ( k6_subset_1 @ ( k9_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['46','47'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('49',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('50',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k6_subset_1 @ X30 @ X31 )
      = ( k4_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('51',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k6_subset_1 @ X30 @ X31 )
      = ( k4_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('52',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k6_subset_1 @ X23 @ ( k6_subset_1 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ( k6_subset_1 @ ( k9_relat_1 @ sk_B @ sk_A ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k9_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['48','52'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('54',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('55',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k6_subset_1 @ X30 @ X31 )
      = ( k4_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('56',plain,(
    ! [X19: $i] :
      ( ( k6_subset_1 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('58',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = ( k3_xboole_0 @ ( k2_relat_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','56','57'])).

thf('59',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k6_subset_1 @ X23 @ ( k6_subset_1 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('60',plain,(
    ! [X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('61',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( ( k10_relat_1 @ X39 @ ( k6_subset_1 @ X40 @ X41 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X39 @ X40 ) @ ( k10_relat_1 @ X39 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('62',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('63',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k6_subset_1 @ X30 @ X31 )
      = ( k4_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('64',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X15 @ X16 ) @ X15 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ ( k6_subset_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k6_subset_1 @ k1_xboole_0 @ X1 ) ) @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','65'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('67',plain,(
    ! [X25: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X25 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('68',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k6_subset_1 @ X30 @ X31 )
      = ( k4_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('69',plain,(
    ! [X25: $i] :
      ( ( k6_subset_1 @ k1_xboole_0 @ X25 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('72',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X8 @ ( k2_xboole_0 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) @ ( k2_xboole_0 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('75',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X22 )
      | ~ ( r1_tarski @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('76',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k6_subset_1 @ X30 @ X31 )
      = ( k4_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('77',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X20 @ X21 ) @ X22 )
      | ~ ( r1_tarski @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k6_subset_1 @ X23 @ ( k6_subset_1 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X19: $i] :
      ( ( k6_subset_1 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('85',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ X26 @ ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('86',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k6_subset_1 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k6_subset_1 @ X23 @ ( k6_subset_1 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X19: $i] :
      ( ( k6_subset_1 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['82','83','84','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['73','92'])).

thf('94',plain,(
    ! [X42: $i,X43: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X42 @ ( k10_relat_1 @ X42 @ X43 ) ) @ X43 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('95',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['45'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['82','83','84','91'])).

thf('97',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X20 @ X21 ) @ X22 )
      | ~ ( r1_tarski @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ ( k6_subset_1 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    r1_tarski @ ( k6_subset_1 @ ( k9_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,
    ( ( k9_relat_1 @ sk_B @ k1_xboole_0 )
    = ( k6_subset_1 @ ( k9_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34','35','36'])).

thf('101',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_B @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('103',plain,
    ( ( k9_relat_1 @ sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['101','102'])).

thf(t157_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) )
          & ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( v2_funct_1 @ C ) )
       => ( r1_tarski @ A @ B ) ) ) )).

thf('104',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( r1_tarski @ X48 @ X49 )
      | ~ ( v1_relat_1 @ X50 )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v2_funct_1 @ X50 )
      | ~ ( r1_tarski @ X48 @ ( k1_relat_1 @ X50 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X50 @ X48 ) @ ( k9_relat_1 @ X50 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[t157_funct_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_B @ X0 ) @ k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v2_funct_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_B @ X0 ) @ k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['105','106','107','108'])).

thf('110',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r1_tarski @ ( k10_relat_1 @ sk_B @ k1_xboole_0 ) @ k1_xboole_0 )
    | ~ ( r1_tarski @ ( k10_relat_1 @ sk_B @ k1_xboole_0 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['94','109'])).

thf('111',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ sk_B @ k1_xboole_0 ) @ k1_xboole_0 )
    | ~ ( r1_tarski @ ( k10_relat_1 @ sk_B @ k1_xboole_0 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('114',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r1_tarski @ ( k10_relat_1 @ sk_B @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['93','113'])).

thf('115',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_B @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('119',plain,
    ( ( k10_relat_1 @ sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['117','118'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('120',plain,(
    ! [X35: $i] :
      ( ( ( k10_relat_1 @ X35 @ ( k2_relat_1 @ X35 ) )
        = ( k1_relat_1 @ X35 ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('121',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( ( k10_relat_1 @ X39 @ ( k6_subset_1 @ X40 @ X41 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X39 @ X40 ) @ ( k10_relat_1 @ X39 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k6_subset_1 @ ( k2_relat_1 @ X0 ) @ X1 ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k6_subset_1 @ ( k2_relat_1 @ X0 ) @ X1 ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k6_subset_1 @ ( k2_relat_1 @ sk_B ) @ k1_xboole_0 ) )
      = ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['119','123'])).

thf('125',plain,(
    ! [X19: $i] :
      ( ( k6_subset_1 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('126',plain,(
    ! [X19: $i] :
      ( ( k6_subset_1 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('127',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['124','125','126','127','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ ( k6_subset_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['61','64'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k6_subset_1 @ ( k2_relat_1 @ sk_B ) @ X0 ) ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k6_subset_1 @ ( k2_relat_1 @ sk_B ) @ X0 ) ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['131','132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_B ) @ X0 ) ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['59','134'])).

thf('136',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ ( k1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['58','135'])).

thf('137',plain,(
    ! [X42: $i,X43: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X42 @ ( k10_relat_1 @ X42 @ X43 ) ) @ X43 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('138',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( r1_tarski @ X48 @ X49 )
      | ~ ( v1_relat_1 @ X50 )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v2_funct_1 @ X50 )
      | ~ ( r1_tarski @ X48 @ ( k1_relat_1 @ X50 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X50 @ X48 ) @ ( k9_relat_1 @ X50 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[t157_funct_1])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['136','140'])).

thf('142',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['141','142','143','144'])).

thf('146',plain,(
    $false ),
    inference(demod,[status(thm)],['8','145'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xvYjyAuf8H
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:38:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.99/1.18  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.99/1.18  % Solved by: fo/fo7.sh
% 0.99/1.18  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.99/1.18  % done 1969 iterations in 0.729s
% 0.99/1.18  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.99/1.18  % SZS output start Refutation
% 0.99/1.18  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.99/1.18  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.99/1.18  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.99/1.18  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.99/1.18  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.99/1.18  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.99/1.18  thf(sk_B_type, type, sk_B: $i).
% 0.99/1.18  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.99/1.18  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.99/1.18  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.99/1.18  thf(sk_A_type, type, sk_A: $i).
% 0.99/1.18  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.99/1.18  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.99/1.18  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.99/1.18  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.99/1.18  thf(t164_funct_1, conjecture,
% 0.99/1.18    (![A:$i,B:$i]:
% 0.99/1.18     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.99/1.18       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.99/1.18         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.99/1.18  thf(zf_stmt_0, negated_conjecture,
% 0.99/1.18    (~( ![A:$i,B:$i]:
% 0.99/1.18        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.99/1.18          ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.99/1.18            ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ) )),
% 0.99/1.18    inference('cnf.neg', [status(esa)], [t164_funct_1])).
% 0.99/1.18  thf('0', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf(t146_funct_1, axiom,
% 0.99/1.18    (![A:$i,B:$i]:
% 0.99/1.18     ( ( v1_relat_1 @ B ) =>
% 0.99/1.18       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.99/1.18         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.99/1.18  thf('1', plain,
% 0.99/1.18      (![X44 : $i, X45 : $i]:
% 0.99/1.18         (~ (r1_tarski @ X44 @ (k1_relat_1 @ X45))
% 0.99/1.18          | (r1_tarski @ X44 @ (k10_relat_1 @ X45 @ (k9_relat_1 @ X45 @ X44)))
% 0.99/1.18          | ~ (v1_relat_1 @ X45))),
% 0.99/1.18      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.99/1.18  thf('2', plain,
% 0.99/1.18      ((~ (v1_relat_1 @ sk_B)
% 0.99/1.18        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 0.99/1.18      inference('sup-', [status(thm)], ['0', '1'])).
% 0.99/1.18  thf('3', plain, ((v1_relat_1 @ sk_B)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('4', plain,
% 0.99/1.18      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.99/1.18      inference('demod', [status(thm)], ['2', '3'])).
% 0.99/1.18  thf(d10_xboole_0, axiom,
% 0.99/1.18    (![A:$i,B:$i]:
% 0.99/1.18     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.99/1.18  thf('5', plain,
% 0.99/1.18      (![X2 : $i, X4 : $i]:
% 0.99/1.18         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.99/1.18      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.99/1.18  thf('6', plain,
% 0.99/1.18      ((~ (r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ sk_A)
% 0.99/1.18        | ((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) = (sk_A)))),
% 0.99/1.18      inference('sup-', [status(thm)], ['4', '5'])).
% 0.99/1.18  thf('7', plain,
% 0.99/1.18      (((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) != (sk_A))),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('8', plain,
% 0.99/1.18      (~ (r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ sk_A)),
% 0.99/1.18      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.99/1.18  thf('9', plain,
% 0.99/1.18      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.99/1.18      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.99/1.18  thf('10', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.99/1.18      inference('simplify', [status(thm)], ['9'])).
% 0.99/1.18  thf(l32_xboole_1, axiom,
% 0.99/1.18    (![A:$i,B:$i]:
% 0.99/1.18     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.99/1.18  thf('11', plain,
% 0.99/1.18      (![X5 : $i, X7 : $i]:
% 0.99/1.18         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.99/1.18      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.99/1.18  thf(redefinition_k6_subset_1, axiom,
% 0.99/1.18    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.99/1.18  thf('12', plain,
% 0.99/1.18      (![X30 : $i, X31 : $i]:
% 0.99/1.18         ((k6_subset_1 @ X30 @ X31) = (k4_xboole_0 @ X30 @ X31))),
% 0.99/1.18      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.99/1.18  thf('13', plain,
% 0.99/1.18      (![X5 : $i, X7 : $i]:
% 0.99/1.18         (((k6_subset_1 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.99/1.18      inference('demod', [status(thm)], ['11', '12'])).
% 0.99/1.18  thf('14', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.99/1.18      inference('sup-', [status(thm)], ['10', '13'])).
% 0.99/1.18  thf(t138_funct_1, axiom,
% 0.99/1.18    (![A:$i,B:$i,C:$i]:
% 0.99/1.18     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.99/1.18       ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 0.99/1.18         ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.99/1.18  thf('15', plain,
% 0.99/1.18      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.99/1.18         (((k10_relat_1 @ X39 @ (k6_subset_1 @ X40 @ X41))
% 0.99/1.18            = (k6_subset_1 @ (k10_relat_1 @ X39 @ X40) @ 
% 0.99/1.18               (k10_relat_1 @ X39 @ X41)))
% 0.99/1.18          | ~ (v1_funct_1 @ X39)
% 0.99/1.18          | ~ (v1_relat_1 @ X39))),
% 0.99/1.18      inference('cnf', [status(esa)], [t138_funct_1])).
% 0.99/1.18  thf('16', plain,
% 0.99/1.18      (![X0 : $i, X1 : $i]:
% 0.99/1.18         (((k10_relat_1 @ X1 @ (k6_subset_1 @ X0 @ X0)) = (k1_xboole_0))
% 0.99/1.18          | ~ (v1_relat_1 @ X1)
% 0.99/1.18          | ~ (v1_funct_1 @ X1))),
% 0.99/1.18      inference('sup+', [status(thm)], ['14', '15'])).
% 0.99/1.18  thf('17', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.99/1.18      inference('sup-', [status(thm)], ['10', '13'])).
% 0.99/1.18  thf('18', plain,
% 0.99/1.18      (![X1 : $i]:
% 0.99/1.18         (((k10_relat_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))
% 0.99/1.18          | ~ (v1_relat_1 @ X1)
% 0.99/1.18          | ~ (v1_funct_1 @ X1))),
% 0.99/1.18      inference('demod', [status(thm)], ['16', '17'])).
% 0.99/1.18  thf(t145_funct_1, axiom,
% 0.99/1.18    (![A:$i,B:$i]:
% 0.99/1.18     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.99/1.18       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 0.99/1.18  thf('19', plain,
% 0.99/1.18      (![X42 : $i, X43 : $i]:
% 0.99/1.18         ((r1_tarski @ (k9_relat_1 @ X42 @ (k10_relat_1 @ X42 @ X43)) @ X43)
% 0.99/1.18          | ~ (v1_funct_1 @ X42)
% 0.99/1.18          | ~ (v1_relat_1 @ X42))),
% 0.99/1.18      inference('cnf', [status(esa)], [t145_funct_1])).
% 0.99/1.18  thf('20', plain,
% 0.99/1.18      (![X0 : $i]:
% 0.99/1.18         ((r1_tarski @ (k9_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.99/1.18          | ~ (v1_funct_1 @ X0)
% 0.99/1.18          | ~ (v1_relat_1 @ X0)
% 0.99/1.18          | ~ (v1_relat_1 @ X0)
% 0.99/1.18          | ~ (v1_funct_1 @ X0))),
% 0.99/1.18      inference('sup+', [status(thm)], ['18', '19'])).
% 0.99/1.18  thf('21', plain,
% 0.99/1.18      (![X0 : $i]:
% 0.99/1.18         (~ (v1_relat_1 @ X0)
% 0.99/1.18          | ~ (v1_funct_1 @ X0)
% 0.99/1.18          | (r1_tarski @ (k9_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.99/1.18      inference('simplify', [status(thm)], ['20'])).
% 0.99/1.18  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.99/1.18  thf('22', plain, (![X14 : $i]: (r1_tarski @ k1_xboole_0 @ X14)),
% 0.99/1.18      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.99/1.18  thf('23', plain,
% 0.99/1.18      (![X2 : $i, X4 : $i]:
% 0.99/1.18         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.99/1.18      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.99/1.18  thf('24', plain,
% 0.99/1.18      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.99/1.18      inference('sup-', [status(thm)], ['22', '23'])).
% 0.99/1.18  thf('25', plain,
% 0.99/1.18      (![X0 : $i]:
% 0.99/1.18         (~ (v1_funct_1 @ X0)
% 0.99/1.18          | ~ (v1_relat_1 @ X0)
% 0.99/1.18          | ((k9_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.99/1.18      inference('sup-', [status(thm)], ['21', '24'])).
% 0.99/1.18  thf('26', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('27', plain,
% 0.99/1.18      (![X5 : $i, X7 : $i]:
% 0.99/1.18         (((k6_subset_1 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.99/1.18      inference('demod', [status(thm)], ['11', '12'])).
% 0.99/1.18  thf('28', plain,
% 0.99/1.18      (((k6_subset_1 @ sk_A @ (k1_relat_1 @ sk_B)) = (k1_xboole_0))),
% 0.99/1.18      inference('sup-', [status(thm)], ['26', '27'])).
% 0.99/1.18  thf(t146_relat_1, axiom,
% 0.99/1.18    (![A:$i]:
% 0.99/1.18     ( ( v1_relat_1 @ A ) =>
% 0.99/1.18       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.99/1.18  thf('29', plain,
% 0.99/1.18      (![X34 : $i]:
% 0.99/1.18         (((k9_relat_1 @ X34 @ (k1_relat_1 @ X34)) = (k2_relat_1 @ X34))
% 0.99/1.18          | ~ (v1_relat_1 @ X34))),
% 0.99/1.18      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.99/1.18  thf(t123_funct_1, axiom,
% 0.99/1.18    (![A:$i,B:$i,C:$i]:
% 0.99/1.18     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.99/1.18       ( ( v2_funct_1 @ C ) =>
% 0.99/1.18         ( ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 0.99/1.18           ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ))).
% 0.99/1.18  thf('30', plain,
% 0.99/1.18      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.99/1.18         (~ (v2_funct_1 @ X36)
% 0.99/1.18          | ((k9_relat_1 @ X36 @ (k6_subset_1 @ X37 @ X38))
% 0.99/1.18              = (k6_subset_1 @ (k9_relat_1 @ X36 @ X37) @ 
% 0.99/1.18                 (k9_relat_1 @ X36 @ X38)))
% 0.99/1.18          | ~ (v1_funct_1 @ X36)
% 0.99/1.18          | ~ (v1_relat_1 @ X36))),
% 0.99/1.18      inference('cnf', [status(esa)], [t123_funct_1])).
% 0.99/1.18  thf('31', plain,
% 0.99/1.18      (![X0 : $i, X1 : $i]:
% 0.99/1.18         (((k9_relat_1 @ X0 @ (k6_subset_1 @ X1 @ (k1_relat_1 @ X0)))
% 0.99/1.18            = (k6_subset_1 @ (k9_relat_1 @ X0 @ X1) @ (k2_relat_1 @ X0)))
% 0.99/1.18          | ~ (v1_relat_1 @ X0)
% 0.99/1.18          | ~ (v1_relat_1 @ X0)
% 0.99/1.18          | ~ (v1_funct_1 @ X0)
% 0.99/1.18          | ~ (v2_funct_1 @ X0))),
% 0.99/1.18      inference('sup+', [status(thm)], ['29', '30'])).
% 0.99/1.18  thf('32', plain,
% 0.99/1.18      (![X0 : $i, X1 : $i]:
% 0.99/1.18         (~ (v2_funct_1 @ X0)
% 0.99/1.18          | ~ (v1_funct_1 @ X0)
% 0.99/1.18          | ~ (v1_relat_1 @ X0)
% 0.99/1.18          | ((k9_relat_1 @ X0 @ (k6_subset_1 @ X1 @ (k1_relat_1 @ X0)))
% 0.99/1.18              = (k6_subset_1 @ (k9_relat_1 @ X0 @ X1) @ (k2_relat_1 @ X0))))),
% 0.99/1.18      inference('simplify', [status(thm)], ['31'])).
% 0.99/1.18  thf('33', plain,
% 0.99/1.18      ((((k9_relat_1 @ sk_B @ k1_xboole_0)
% 0.99/1.18          = (k6_subset_1 @ (k9_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B)))
% 0.99/1.18        | ~ (v1_relat_1 @ sk_B)
% 0.99/1.18        | ~ (v1_funct_1 @ sk_B)
% 0.99/1.18        | ~ (v2_funct_1 @ sk_B))),
% 0.99/1.18      inference('sup+', [status(thm)], ['28', '32'])).
% 0.99/1.18  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('35', plain, ((v1_funct_1 @ sk_B)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('36', plain, ((v2_funct_1 @ sk_B)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('37', plain,
% 0.99/1.18      (((k9_relat_1 @ sk_B @ k1_xboole_0)
% 0.99/1.18         = (k6_subset_1 @ (k9_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 0.99/1.18      inference('demod', [status(thm)], ['33', '34', '35', '36'])).
% 0.99/1.18  thf('38', plain,
% 0.99/1.18      (![X5 : $i, X6 : $i]:
% 0.99/1.18         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 0.99/1.18      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.99/1.18  thf('39', plain,
% 0.99/1.18      (![X30 : $i, X31 : $i]:
% 0.99/1.18         ((k6_subset_1 @ X30 @ X31) = (k4_xboole_0 @ X30 @ X31))),
% 0.99/1.18      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.99/1.18  thf('40', plain,
% 0.99/1.18      (![X5 : $i, X6 : $i]:
% 0.99/1.18         ((r1_tarski @ X5 @ X6) | ((k6_subset_1 @ X5 @ X6) != (k1_xboole_0)))),
% 0.99/1.18      inference('demod', [status(thm)], ['38', '39'])).
% 0.99/1.18  thf('41', plain,
% 0.99/1.18      ((((k9_relat_1 @ sk_B @ k1_xboole_0) != (k1_xboole_0))
% 0.99/1.18        | (r1_tarski @ (k9_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 0.99/1.18      inference('sup-', [status(thm)], ['37', '40'])).
% 0.99/1.18  thf('42', plain,
% 0.99/1.18      ((((k1_xboole_0) != (k1_xboole_0))
% 0.99/1.18        | ~ (v1_relat_1 @ sk_B)
% 0.99/1.18        | ~ (v1_funct_1 @ sk_B)
% 0.99/1.18        | (r1_tarski @ (k9_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 0.99/1.18      inference('sup-', [status(thm)], ['25', '41'])).
% 0.99/1.18  thf('43', plain, ((v1_relat_1 @ sk_B)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('44', plain, ((v1_funct_1 @ sk_B)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('45', plain,
% 0.99/1.18      ((((k1_xboole_0) != (k1_xboole_0))
% 0.99/1.18        | (r1_tarski @ (k9_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 0.99/1.18      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.99/1.18  thf('46', plain,
% 0.99/1.18      ((r1_tarski @ (k9_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))),
% 0.99/1.18      inference('simplify', [status(thm)], ['45'])).
% 0.99/1.18  thf('47', plain,
% 0.99/1.18      (![X5 : $i, X7 : $i]:
% 0.99/1.18         (((k6_subset_1 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.99/1.18      inference('demod', [status(thm)], ['11', '12'])).
% 0.99/1.18  thf('48', plain,
% 0.99/1.18      (((k6_subset_1 @ (k9_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))
% 0.99/1.18         = (k1_xboole_0))),
% 0.99/1.18      inference('sup-', [status(thm)], ['46', '47'])).
% 0.99/1.18  thf(t48_xboole_1, axiom,
% 0.99/1.18    (![A:$i,B:$i]:
% 0.99/1.18     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.99/1.18  thf('49', plain,
% 0.99/1.18      (![X23 : $i, X24 : $i]:
% 0.99/1.18         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 0.99/1.18           = (k3_xboole_0 @ X23 @ X24))),
% 0.99/1.18      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.99/1.18  thf('50', plain,
% 0.99/1.18      (![X30 : $i, X31 : $i]:
% 0.99/1.18         ((k6_subset_1 @ X30 @ X31) = (k4_xboole_0 @ X30 @ X31))),
% 0.99/1.18      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.99/1.18  thf('51', plain,
% 0.99/1.18      (![X30 : $i, X31 : $i]:
% 0.99/1.18         ((k6_subset_1 @ X30 @ X31) = (k4_xboole_0 @ X30 @ X31))),
% 0.99/1.18      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.99/1.18  thf('52', plain,
% 0.99/1.18      (![X23 : $i, X24 : $i]:
% 0.99/1.18         ((k6_subset_1 @ X23 @ (k6_subset_1 @ X23 @ X24))
% 0.99/1.18           = (k3_xboole_0 @ X23 @ X24))),
% 0.99/1.18      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.99/1.18  thf('53', plain,
% 0.99/1.18      (((k6_subset_1 @ (k9_relat_1 @ sk_B @ sk_A) @ k1_xboole_0)
% 0.99/1.18         = (k3_xboole_0 @ (k9_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 0.99/1.18      inference('sup+', [status(thm)], ['48', '52'])).
% 0.99/1.18  thf(t3_boole, axiom,
% 0.99/1.18    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.99/1.18  thf('54', plain, (![X19 : $i]: ((k4_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.99/1.18      inference('cnf', [status(esa)], [t3_boole])).
% 0.99/1.18  thf('55', plain,
% 0.99/1.18      (![X30 : $i, X31 : $i]:
% 0.99/1.18         ((k6_subset_1 @ X30 @ X31) = (k4_xboole_0 @ X30 @ X31))),
% 0.99/1.18      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.99/1.18  thf('56', plain, (![X19 : $i]: ((k6_subset_1 @ X19 @ k1_xboole_0) = (X19))),
% 0.99/1.18      inference('demod', [status(thm)], ['54', '55'])).
% 0.99/1.18  thf(commutativity_k3_xboole_0, axiom,
% 0.99/1.18    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.99/1.18  thf('57', plain,
% 0.99/1.18      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.99/1.18      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.99/1.18  thf('58', plain,
% 0.99/1.18      (((k9_relat_1 @ sk_B @ sk_A)
% 0.99/1.18         = (k3_xboole_0 @ (k2_relat_1 @ sk_B) @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.99/1.18      inference('demod', [status(thm)], ['53', '56', '57'])).
% 0.99/1.18  thf('59', plain,
% 0.99/1.18      (![X23 : $i, X24 : $i]:
% 0.99/1.18         ((k6_subset_1 @ X23 @ (k6_subset_1 @ X23 @ X24))
% 0.99/1.18           = (k3_xboole_0 @ X23 @ X24))),
% 0.99/1.18      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.99/1.18  thf('60', plain,
% 0.99/1.18      (![X1 : $i]:
% 0.99/1.18         (((k10_relat_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))
% 0.99/1.18          | ~ (v1_relat_1 @ X1)
% 0.99/1.18          | ~ (v1_funct_1 @ X1))),
% 0.99/1.18      inference('demod', [status(thm)], ['16', '17'])).
% 0.99/1.18  thf('61', plain,
% 0.99/1.18      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.99/1.18         (((k10_relat_1 @ X39 @ (k6_subset_1 @ X40 @ X41))
% 0.99/1.18            = (k6_subset_1 @ (k10_relat_1 @ X39 @ X40) @ 
% 0.99/1.18               (k10_relat_1 @ X39 @ X41)))
% 0.99/1.18          | ~ (v1_funct_1 @ X39)
% 0.99/1.18          | ~ (v1_relat_1 @ X39))),
% 0.99/1.18      inference('cnf', [status(esa)], [t138_funct_1])).
% 0.99/1.18  thf(t36_xboole_1, axiom,
% 0.99/1.18    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.99/1.18  thf('62', plain,
% 0.99/1.18      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 0.99/1.18      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.99/1.18  thf('63', plain,
% 0.99/1.18      (![X30 : $i, X31 : $i]:
% 0.99/1.18         ((k6_subset_1 @ X30 @ X31) = (k4_xboole_0 @ X30 @ X31))),
% 0.99/1.18      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.99/1.18  thf('64', plain,
% 0.99/1.18      (![X15 : $i, X16 : $i]: (r1_tarski @ (k6_subset_1 @ X15 @ X16) @ X15)),
% 0.99/1.18      inference('demod', [status(thm)], ['62', '63'])).
% 0.99/1.18  thf('65', plain,
% 0.99/1.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.18         ((r1_tarski @ (k10_relat_1 @ X2 @ (k6_subset_1 @ X1 @ X0)) @ 
% 0.99/1.18           (k10_relat_1 @ X2 @ X1))
% 0.99/1.18          | ~ (v1_relat_1 @ X2)
% 0.99/1.18          | ~ (v1_funct_1 @ X2))),
% 0.99/1.18      inference('sup+', [status(thm)], ['61', '64'])).
% 0.99/1.18  thf('66', plain,
% 0.99/1.18      (![X0 : $i, X1 : $i]:
% 0.99/1.18         ((r1_tarski @ (k10_relat_1 @ X0 @ (k6_subset_1 @ k1_xboole_0 @ X1)) @ 
% 0.99/1.18           k1_xboole_0)
% 0.99/1.18          | ~ (v1_funct_1 @ X0)
% 0.99/1.18          | ~ (v1_relat_1 @ X0)
% 0.99/1.18          | ~ (v1_funct_1 @ X0)
% 0.99/1.18          | ~ (v1_relat_1 @ X0))),
% 0.99/1.18      inference('sup+', [status(thm)], ['60', '65'])).
% 0.99/1.18  thf(t4_boole, axiom,
% 0.99/1.18    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.99/1.18  thf('67', plain,
% 0.99/1.18      (![X25 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X25) = (k1_xboole_0))),
% 0.99/1.18      inference('cnf', [status(esa)], [t4_boole])).
% 0.99/1.18  thf('68', plain,
% 0.99/1.18      (![X30 : $i, X31 : $i]:
% 0.99/1.18         ((k6_subset_1 @ X30 @ X31) = (k4_xboole_0 @ X30 @ X31))),
% 0.99/1.18      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.99/1.18  thf('69', plain,
% 0.99/1.18      (![X25 : $i]: ((k6_subset_1 @ k1_xboole_0 @ X25) = (k1_xboole_0))),
% 0.99/1.18      inference('demod', [status(thm)], ['67', '68'])).
% 0.99/1.18  thf('70', plain,
% 0.99/1.18      (![X0 : $i]:
% 0.99/1.18         ((r1_tarski @ (k10_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.99/1.18          | ~ (v1_funct_1 @ X0)
% 0.99/1.18          | ~ (v1_relat_1 @ X0)
% 0.99/1.18          | ~ (v1_funct_1 @ X0)
% 0.99/1.18          | ~ (v1_relat_1 @ X0))),
% 0.99/1.18      inference('demod', [status(thm)], ['66', '69'])).
% 0.99/1.18  thf('71', plain,
% 0.99/1.18      (![X0 : $i]:
% 0.99/1.18         (~ (v1_relat_1 @ X0)
% 0.99/1.18          | ~ (v1_funct_1 @ X0)
% 0.99/1.18          | (r1_tarski @ (k10_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.99/1.18      inference('simplify', [status(thm)], ['70'])).
% 0.99/1.18  thf(t10_xboole_1, axiom,
% 0.99/1.18    (![A:$i,B:$i,C:$i]:
% 0.99/1.18     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.99/1.18  thf('72', plain,
% 0.99/1.18      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.99/1.18         (~ (r1_tarski @ X8 @ X9) | (r1_tarski @ X8 @ (k2_xboole_0 @ X10 @ X9)))),
% 0.99/1.18      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.99/1.18  thf('73', plain,
% 0.99/1.18      (![X0 : $i, X1 : $i]:
% 0.99/1.18         (~ (v1_funct_1 @ X0)
% 0.99/1.18          | ~ (v1_relat_1 @ X0)
% 0.99/1.18          | (r1_tarski @ (k10_relat_1 @ X0 @ k1_xboole_0) @ 
% 0.99/1.18             (k2_xboole_0 @ X1 @ k1_xboole_0)))),
% 0.99/1.18      inference('sup-', [status(thm)], ['71', '72'])).
% 0.99/1.18  thf('74', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.99/1.18      inference('simplify', [status(thm)], ['9'])).
% 0.99/1.18  thf(t43_xboole_1, axiom,
% 0.99/1.18    (![A:$i,B:$i,C:$i]:
% 0.99/1.18     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.99/1.18       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.99/1.18  thf('75', plain,
% 0.99/1.18      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.99/1.18         ((r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X22)
% 0.99/1.18          | ~ (r1_tarski @ X20 @ (k2_xboole_0 @ X21 @ X22)))),
% 0.99/1.18      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.99/1.18  thf('76', plain,
% 0.99/1.18      (![X30 : $i, X31 : $i]:
% 0.99/1.18         ((k6_subset_1 @ X30 @ X31) = (k4_xboole_0 @ X30 @ X31))),
% 0.99/1.18      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.99/1.18  thf('77', plain,
% 0.99/1.18      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.99/1.18         ((r1_tarski @ (k6_subset_1 @ X20 @ X21) @ X22)
% 0.99/1.18          | ~ (r1_tarski @ X20 @ (k2_xboole_0 @ X21 @ X22)))),
% 0.99/1.18      inference('demod', [status(thm)], ['75', '76'])).
% 0.99/1.18  thf('78', plain,
% 0.99/1.18      (![X0 : $i, X1 : $i]:
% 0.99/1.18         (r1_tarski @ (k6_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)),
% 0.99/1.18      inference('sup-', [status(thm)], ['74', '77'])).
% 0.99/1.18  thf('79', plain,
% 0.99/1.18      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.99/1.18      inference('sup-', [status(thm)], ['22', '23'])).
% 0.99/1.18  thf('80', plain,
% 0.99/1.18      (![X0 : $i]:
% 0.99/1.18         ((k6_subset_1 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0) = (k1_xboole_0))),
% 0.99/1.18      inference('sup-', [status(thm)], ['78', '79'])).
% 0.99/1.18  thf('81', plain,
% 0.99/1.18      (![X23 : $i, X24 : $i]:
% 0.99/1.18         ((k6_subset_1 @ X23 @ (k6_subset_1 @ X23 @ X24))
% 0.99/1.18           = (k3_xboole_0 @ X23 @ X24))),
% 0.99/1.18      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.99/1.18  thf('82', plain,
% 0.99/1.18      (![X0 : $i]:
% 0.99/1.18         ((k6_subset_1 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.99/1.18           = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0))),
% 0.99/1.18      inference('sup+', [status(thm)], ['80', '81'])).
% 0.99/1.18  thf('83', plain, (![X19 : $i]: ((k6_subset_1 @ X19 @ k1_xboole_0) = (X19))),
% 0.99/1.18      inference('demod', [status(thm)], ['54', '55'])).
% 0.99/1.18  thf('84', plain,
% 0.99/1.18      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.99/1.18      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.99/1.18  thf(t7_xboole_1, axiom,
% 0.99/1.18    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.99/1.18  thf('85', plain,
% 0.99/1.18      (![X26 : $i, X27 : $i]: (r1_tarski @ X26 @ (k2_xboole_0 @ X26 @ X27))),
% 0.99/1.18      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.99/1.18  thf('86', plain,
% 0.99/1.18      (![X5 : $i, X7 : $i]:
% 0.99/1.18         (((k6_subset_1 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.99/1.18      inference('demod', [status(thm)], ['11', '12'])).
% 0.99/1.18  thf('87', plain,
% 0.99/1.18      (![X0 : $i, X1 : $i]:
% 0.99/1.18         ((k6_subset_1 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.99/1.18      inference('sup-', [status(thm)], ['85', '86'])).
% 0.99/1.18  thf('88', plain,
% 0.99/1.18      (![X23 : $i, X24 : $i]:
% 0.99/1.18         ((k6_subset_1 @ X23 @ (k6_subset_1 @ X23 @ X24))
% 0.99/1.18           = (k3_xboole_0 @ X23 @ X24))),
% 0.99/1.18      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.99/1.18  thf('89', plain,
% 0.99/1.18      (![X0 : $i, X1 : $i]:
% 0.99/1.18         ((k6_subset_1 @ X1 @ k1_xboole_0)
% 0.99/1.18           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.99/1.18      inference('sup+', [status(thm)], ['87', '88'])).
% 0.99/1.18  thf('90', plain, (![X19 : $i]: ((k6_subset_1 @ X19 @ k1_xboole_0) = (X19))),
% 0.99/1.18      inference('demod', [status(thm)], ['54', '55'])).
% 0.99/1.18  thf('91', plain,
% 0.99/1.18      (![X0 : $i, X1 : $i]:
% 0.99/1.18         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.99/1.18      inference('demod', [status(thm)], ['89', '90'])).
% 0.99/1.18  thf('92', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.99/1.18      inference('demod', [status(thm)], ['82', '83', '84', '91'])).
% 0.99/1.18  thf('93', plain,
% 0.99/1.18      (![X0 : $i, X1 : $i]:
% 0.99/1.18         (~ (v1_funct_1 @ X0)
% 0.99/1.18          | ~ (v1_relat_1 @ X0)
% 0.99/1.18          | (r1_tarski @ (k10_relat_1 @ X0 @ k1_xboole_0) @ X1))),
% 0.99/1.18      inference('demod', [status(thm)], ['73', '92'])).
% 0.99/1.18  thf('94', plain,
% 0.99/1.18      (![X42 : $i, X43 : $i]:
% 0.99/1.18         ((r1_tarski @ (k9_relat_1 @ X42 @ (k10_relat_1 @ X42 @ X43)) @ X43)
% 0.99/1.18          | ~ (v1_funct_1 @ X42)
% 0.99/1.18          | ~ (v1_relat_1 @ X42))),
% 0.99/1.18      inference('cnf', [status(esa)], [t145_funct_1])).
% 0.99/1.18  thf('95', plain,
% 0.99/1.18      ((r1_tarski @ (k9_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))),
% 0.99/1.18      inference('simplify', [status(thm)], ['45'])).
% 0.99/1.18  thf('96', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.99/1.18      inference('demod', [status(thm)], ['82', '83', '84', '91'])).
% 0.99/1.18  thf('97', plain,
% 0.99/1.18      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.99/1.18         ((r1_tarski @ (k6_subset_1 @ X20 @ X21) @ X22)
% 0.99/1.18          | ~ (r1_tarski @ X20 @ (k2_xboole_0 @ X21 @ X22)))),
% 0.99/1.18      inference('demod', [status(thm)], ['75', '76'])).
% 0.99/1.18  thf('98', plain,
% 0.99/1.18      (![X0 : $i, X1 : $i]:
% 0.99/1.18         (~ (r1_tarski @ X1 @ X0)
% 0.99/1.18          | (r1_tarski @ (k6_subset_1 @ X1 @ X0) @ k1_xboole_0))),
% 0.99/1.18      inference('sup-', [status(thm)], ['96', '97'])).
% 0.99/1.18  thf('99', plain,
% 0.99/1.18      ((r1_tarski @ 
% 0.99/1.18        (k6_subset_1 @ (k9_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B)) @ 
% 0.99/1.18        k1_xboole_0)),
% 0.99/1.18      inference('sup-', [status(thm)], ['95', '98'])).
% 0.99/1.18  thf('100', plain,
% 0.99/1.18      (((k9_relat_1 @ sk_B @ k1_xboole_0)
% 0.99/1.18         = (k6_subset_1 @ (k9_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 0.99/1.18      inference('demod', [status(thm)], ['33', '34', '35', '36'])).
% 0.99/1.18  thf('101', plain,
% 0.99/1.18      ((r1_tarski @ (k9_relat_1 @ sk_B @ k1_xboole_0) @ k1_xboole_0)),
% 0.99/1.18      inference('demod', [status(thm)], ['99', '100'])).
% 0.99/1.18  thf('102', plain,
% 0.99/1.18      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.99/1.18      inference('sup-', [status(thm)], ['22', '23'])).
% 0.99/1.18  thf('103', plain, (((k9_relat_1 @ sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.99/1.18      inference('sup-', [status(thm)], ['101', '102'])).
% 0.99/1.18  thf(t157_funct_1, axiom,
% 0.99/1.18    (![A:$i,B:$i,C:$i]:
% 0.99/1.18     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.99/1.18       ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.99/1.18           ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.99/1.18         ( r1_tarski @ A @ B ) ) ))).
% 0.99/1.18  thf('104', plain,
% 0.99/1.18      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.99/1.18         ((r1_tarski @ X48 @ X49)
% 0.99/1.18          | ~ (v1_relat_1 @ X50)
% 0.99/1.18          | ~ (v1_funct_1 @ X50)
% 0.99/1.18          | ~ (v2_funct_1 @ X50)
% 0.99/1.18          | ~ (r1_tarski @ X48 @ (k1_relat_1 @ X50))
% 0.99/1.18          | ~ (r1_tarski @ (k9_relat_1 @ X50 @ X48) @ (k9_relat_1 @ X50 @ X49)))),
% 0.99/1.18      inference('cnf', [status(esa)], [t157_funct_1])).
% 0.99/1.18  thf('105', plain,
% 0.99/1.18      (![X0 : $i]:
% 0.99/1.18         (~ (r1_tarski @ (k9_relat_1 @ sk_B @ X0) @ k1_xboole_0)
% 0.99/1.18          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_B))
% 0.99/1.18          | ~ (v2_funct_1 @ sk_B)
% 0.99/1.18          | ~ (v1_funct_1 @ sk_B)
% 0.99/1.18          | ~ (v1_relat_1 @ sk_B)
% 0.99/1.18          | (r1_tarski @ X0 @ k1_xboole_0))),
% 0.99/1.18      inference('sup-', [status(thm)], ['103', '104'])).
% 0.99/1.18  thf('106', plain, ((v2_funct_1 @ sk_B)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('107', plain, ((v1_funct_1 @ sk_B)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('108', plain, ((v1_relat_1 @ sk_B)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('109', plain,
% 0.99/1.18      (![X0 : $i]:
% 0.99/1.18         (~ (r1_tarski @ (k9_relat_1 @ sk_B @ X0) @ k1_xboole_0)
% 0.99/1.18          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_B))
% 0.99/1.18          | (r1_tarski @ X0 @ k1_xboole_0))),
% 0.99/1.18      inference('demod', [status(thm)], ['105', '106', '107', '108'])).
% 0.99/1.18  thf('110', plain,
% 0.99/1.18      ((~ (v1_relat_1 @ sk_B)
% 0.99/1.18        | ~ (v1_funct_1 @ sk_B)
% 0.99/1.18        | (r1_tarski @ (k10_relat_1 @ sk_B @ k1_xboole_0) @ k1_xboole_0)
% 0.99/1.18        | ~ (r1_tarski @ (k10_relat_1 @ sk_B @ k1_xboole_0) @ 
% 0.99/1.18             (k1_relat_1 @ sk_B)))),
% 0.99/1.18      inference('sup-', [status(thm)], ['94', '109'])).
% 0.99/1.18  thf('111', plain, ((v1_relat_1 @ sk_B)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('112', plain, ((v1_funct_1 @ sk_B)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('113', plain,
% 0.99/1.18      (((r1_tarski @ (k10_relat_1 @ sk_B @ k1_xboole_0) @ k1_xboole_0)
% 0.99/1.18        | ~ (r1_tarski @ (k10_relat_1 @ sk_B @ k1_xboole_0) @ 
% 0.99/1.18             (k1_relat_1 @ sk_B)))),
% 0.99/1.18      inference('demod', [status(thm)], ['110', '111', '112'])).
% 0.99/1.18  thf('114', plain,
% 0.99/1.18      ((~ (v1_relat_1 @ sk_B)
% 0.99/1.18        | ~ (v1_funct_1 @ sk_B)
% 0.99/1.18        | (r1_tarski @ (k10_relat_1 @ sk_B @ k1_xboole_0) @ k1_xboole_0))),
% 0.99/1.18      inference('sup-', [status(thm)], ['93', '113'])).
% 0.99/1.18  thf('115', plain, ((v1_relat_1 @ sk_B)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('116', plain, ((v1_funct_1 @ sk_B)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('117', plain,
% 0.99/1.18      ((r1_tarski @ (k10_relat_1 @ sk_B @ k1_xboole_0) @ k1_xboole_0)),
% 0.99/1.18      inference('demod', [status(thm)], ['114', '115', '116'])).
% 0.99/1.18  thf('118', plain,
% 0.99/1.18      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.99/1.18      inference('sup-', [status(thm)], ['22', '23'])).
% 0.99/1.18  thf('119', plain, (((k10_relat_1 @ sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.99/1.18      inference('sup-', [status(thm)], ['117', '118'])).
% 0.99/1.18  thf(t169_relat_1, axiom,
% 0.99/1.18    (![A:$i]:
% 0.99/1.18     ( ( v1_relat_1 @ A ) =>
% 0.99/1.18       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.99/1.18  thf('120', plain,
% 0.99/1.18      (![X35 : $i]:
% 0.99/1.18         (((k10_relat_1 @ X35 @ (k2_relat_1 @ X35)) = (k1_relat_1 @ X35))
% 0.99/1.18          | ~ (v1_relat_1 @ X35))),
% 0.99/1.18      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.99/1.18  thf('121', plain,
% 0.99/1.18      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.99/1.18         (((k10_relat_1 @ X39 @ (k6_subset_1 @ X40 @ X41))
% 0.99/1.18            = (k6_subset_1 @ (k10_relat_1 @ X39 @ X40) @ 
% 0.99/1.18               (k10_relat_1 @ X39 @ X41)))
% 0.99/1.18          | ~ (v1_funct_1 @ X39)
% 0.99/1.18          | ~ (v1_relat_1 @ X39))),
% 0.99/1.18      inference('cnf', [status(esa)], [t138_funct_1])).
% 0.99/1.18  thf('122', plain,
% 0.99/1.18      (![X0 : $i, X1 : $i]:
% 0.99/1.18         (((k10_relat_1 @ X0 @ (k6_subset_1 @ (k2_relat_1 @ X0) @ X1))
% 0.99/1.18            = (k6_subset_1 @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1)))
% 0.99/1.18          | ~ (v1_relat_1 @ X0)
% 0.99/1.18          | ~ (v1_relat_1 @ X0)
% 0.99/1.18          | ~ (v1_funct_1 @ X0))),
% 0.99/1.18      inference('sup+', [status(thm)], ['120', '121'])).
% 0.99/1.18  thf('123', plain,
% 0.99/1.18      (![X0 : $i, X1 : $i]:
% 0.99/1.18         (~ (v1_funct_1 @ X0)
% 0.99/1.18          | ~ (v1_relat_1 @ X0)
% 0.99/1.18          | ((k10_relat_1 @ X0 @ (k6_subset_1 @ (k2_relat_1 @ X0) @ X1))
% 0.99/1.18              = (k6_subset_1 @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))))),
% 0.99/1.18      inference('simplify', [status(thm)], ['122'])).
% 0.99/1.18  thf('124', plain,
% 0.99/1.18      ((((k10_relat_1 @ sk_B @ 
% 0.99/1.18          (k6_subset_1 @ (k2_relat_1 @ sk_B) @ k1_xboole_0))
% 0.99/1.18          = (k6_subset_1 @ (k1_relat_1 @ sk_B) @ k1_xboole_0))
% 0.99/1.18        | ~ (v1_relat_1 @ sk_B)
% 0.99/1.18        | ~ (v1_funct_1 @ sk_B))),
% 0.99/1.18      inference('sup+', [status(thm)], ['119', '123'])).
% 0.99/1.18  thf('125', plain, (![X19 : $i]: ((k6_subset_1 @ X19 @ k1_xboole_0) = (X19))),
% 0.99/1.18      inference('demod', [status(thm)], ['54', '55'])).
% 0.99/1.18  thf('126', plain, (![X19 : $i]: ((k6_subset_1 @ X19 @ k1_xboole_0) = (X19))),
% 0.99/1.18      inference('demod', [status(thm)], ['54', '55'])).
% 0.99/1.18  thf('127', plain, ((v1_relat_1 @ sk_B)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('128', plain, ((v1_funct_1 @ sk_B)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('129', plain,
% 0.99/1.18      (((k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)) = (k1_relat_1 @ sk_B))),
% 0.99/1.18      inference('demod', [status(thm)], ['124', '125', '126', '127', '128'])).
% 0.99/1.18  thf('130', plain,
% 0.99/1.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.18         ((r1_tarski @ (k10_relat_1 @ X2 @ (k6_subset_1 @ X1 @ X0)) @ 
% 0.99/1.18           (k10_relat_1 @ X2 @ X1))
% 0.99/1.18          | ~ (v1_relat_1 @ X2)
% 0.99/1.18          | ~ (v1_funct_1 @ X2))),
% 0.99/1.18      inference('sup+', [status(thm)], ['61', '64'])).
% 0.99/1.18  thf('131', plain,
% 0.99/1.18      (![X0 : $i]:
% 0.99/1.18         ((r1_tarski @ 
% 0.99/1.18           (k10_relat_1 @ sk_B @ (k6_subset_1 @ (k2_relat_1 @ sk_B) @ X0)) @ 
% 0.99/1.18           (k1_relat_1 @ sk_B))
% 0.99/1.18          | ~ (v1_funct_1 @ sk_B)
% 0.99/1.18          | ~ (v1_relat_1 @ sk_B))),
% 0.99/1.18      inference('sup+', [status(thm)], ['129', '130'])).
% 0.99/1.18  thf('132', plain, ((v1_funct_1 @ sk_B)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('133', plain, ((v1_relat_1 @ sk_B)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('134', plain,
% 0.99/1.18      (![X0 : $i]:
% 0.99/1.18         (r1_tarski @ 
% 0.99/1.18          (k10_relat_1 @ sk_B @ (k6_subset_1 @ (k2_relat_1 @ sk_B) @ X0)) @ 
% 0.99/1.18          (k1_relat_1 @ sk_B))),
% 0.99/1.18      inference('demod', [status(thm)], ['131', '132', '133'])).
% 0.99/1.18  thf('135', plain,
% 0.99/1.18      (![X0 : $i]:
% 0.99/1.18         (r1_tarski @ 
% 0.99/1.18          (k10_relat_1 @ sk_B @ (k3_xboole_0 @ (k2_relat_1 @ sk_B) @ X0)) @ 
% 0.99/1.18          (k1_relat_1 @ sk_B))),
% 0.99/1.18      inference('sup+', [status(thm)], ['59', '134'])).
% 0.99/1.18  thf('136', plain,
% 0.99/1.18      ((r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ 
% 0.99/1.18        (k1_relat_1 @ sk_B))),
% 0.99/1.18      inference('sup+', [status(thm)], ['58', '135'])).
% 0.99/1.18  thf('137', plain,
% 0.99/1.18      (![X42 : $i, X43 : $i]:
% 0.99/1.18         ((r1_tarski @ (k9_relat_1 @ X42 @ (k10_relat_1 @ X42 @ X43)) @ X43)
% 0.99/1.18          | ~ (v1_funct_1 @ X42)
% 0.99/1.18          | ~ (v1_relat_1 @ X42))),
% 0.99/1.18      inference('cnf', [status(esa)], [t145_funct_1])).
% 0.99/1.18  thf('138', plain,
% 0.99/1.18      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.99/1.18         ((r1_tarski @ X48 @ X49)
% 0.99/1.18          | ~ (v1_relat_1 @ X50)
% 0.99/1.18          | ~ (v1_funct_1 @ X50)
% 0.99/1.18          | ~ (v2_funct_1 @ X50)
% 0.99/1.18          | ~ (r1_tarski @ X48 @ (k1_relat_1 @ X50))
% 0.99/1.18          | ~ (r1_tarski @ (k9_relat_1 @ X50 @ X48) @ (k9_relat_1 @ X50 @ X49)))),
% 0.99/1.18      inference('cnf', [status(esa)], [t157_funct_1])).
% 0.99/1.18  thf('139', plain,
% 0.99/1.18      (![X0 : $i, X1 : $i]:
% 0.99/1.18         (~ (v1_relat_1 @ X1)
% 0.99/1.18          | ~ (v1_funct_1 @ X1)
% 0.99/1.18          | ~ (r1_tarski @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ 
% 0.99/1.18               (k1_relat_1 @ X1))
% 0.99/1.18          | ~ (v2_funct_1 @ X1)
% 0.99/1.18          | ~ (v1_funct_1 @ X1)
% 0.99/1.18          | ~ (v1_relat_1 @ X1)
% 0.99/1.18          | (r1_tarski @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ X0))),
% 0.99/1.18      inference('sup-', [status(thm)], ['137', '138'])).
% 0.99/1.18  thf('140', plain,
% 0.99/1.18      (![X0 : $i, X1 : $i]:
% 0.99/1.18         ((r1_tarski @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ X0)
% 0.99/1.18          | ~ (v2_funct_1 @ X1)
% 0.99/1.18          | ~ (r1_tarski @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ 
% 0.99/1.18               (k1_relat_1 @ X1))
% 0.99/1.18          | ~ (v1_funct_1 @ X1)
% 0.99/1.18          | ~ (v1_relat_1 @ X1))),
% 0.99/1.18      inference('simplify', [status(thm)], ['139'])).
% 0.99/1.18  thf('141', plain,
% 0.99/1.18      ((~ (v1_relat_1 @ sk_B)
% 0.99/1.18        | ~ (v1_funct_1 @ sk_B)
% 0.99/1.18        | ~ (v2_funct_1 @ sk_B)
% 0.99/1.18        | (r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ sk_A))),
% 0.99/1.18      inference('sup-', [status(thm)], ['136', '140'])).
% 0.99/1.18  thf('142', plain, ((v1_relat_1 @ sk_B)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('143', plain, ((v1_funct_1 @ sk_B)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('144', plain, ((v2_funct_1 @ sk_B)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('145', plain,
% 0.99/1.18      ((r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ sk_A)),
% 0.99/1.18      inference('demod', [status(thm)], ['141', '142', '143', '144'])).
% 0.99/1.18  thf('146', plain, ($false), inference('demod', [status(thm)], ['8', '145'])).
% 0.99/1.18  
% 0.99/1.18  % SZS output end Refutation
% 0.99/1.18  
% 0.99/1.19  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
