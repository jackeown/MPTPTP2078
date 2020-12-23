%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EN3hv4rIbV

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:30 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 150 expanded)
%              Number of leaves         :   27 (  57 expanded)
%              Depth                    :   23
%              Number of atoms          :  762 (1308 expanded)
%              Number of equality atoms :   59 ( 109 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t138_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('0',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k10_relat_1 @ X32 @ ( k6_subset_1 @ X33 @ X34 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X32 @ X33 ) @ ( k10_relat_1 @ X32 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X27: $i] :
      ( ( ( k10_relat_1 @ X27 @ ( k2_relat_1 @ X27 ) )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('2',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k6_subset_1 @ X23 @ X24 )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,(
    ! [X5: $i] :
      ( ( k6_subset_1 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X11: $i,X13: $i] :
      ( ( r1_xboole_0 @ X11 @ X13 )
      | ( ( k4_xboole_0 @ X11 @ X13 )
       != X11 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('6',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k6_subset_1 @ X23 @ X24 )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('7',plain,(
    ! [X11: $i,X13: $i] :
      ( ( r1_xboole_0 @ X11 @ X13 )
      | ( ( k6_subset_1 @ X11 @ X13 )
       != X11 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( X0 != X0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t173_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k10_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('10',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_relat_1 @ X30 ) @ X31 )
      | ( ( k10_relat_1 @ X30 @ X31 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t173_relat_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t147_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
         => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t147_funct_1])).

thf('12',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('14',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k6_subset_1 @ X23 @ X24 )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('15',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k6_subset_1 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k6_subset_1 @ sk_A @ ( k2_relat_1 @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k10_relat_1 @ X32 @ ( k6_subset_1 @ X33 @ X34 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X32 @ X33 ) @ ( k10_relat_1 @ X32 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( ( k4_xboole_0 @ X2 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('19',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k6_subset_1 @ X23 @ X24 )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( ( k6_subset_1 @ X2 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ X2 @ ( k6_subset_1 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( r1_tarski @ ( k10_relat_1 @ X2 @ X1 ) @ ( k10_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ sk_A ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ sk_A ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['11','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ sk_A ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['1','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('30',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( r1_tarski @ X37 @ ( k1_relat_1 @ X38 ) )
      | ( r1_tarski @ X37 @ ( k10_relat_1 @ X38 @ ( k9_relat_1 @ X38 @ X37 ) ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ ( k10_relat_1 @ sk_B @ sk_A ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_B @ sk_A ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k6_subset_1 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('35',plain,
    ( ( k6_subset_1 @ ( k10_relat_1 @ sk_B @ sk_A ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k6_subset_1 @ sk_A @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k10_relat_1 @ sk_B @ ( k6_subset_1 @ sk_A @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k10_relat_1 @ X30 @ X31 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ X30 ) @ X31 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t173_relat_1])).

thf('41',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ ( k6_subset_1 @ sk_A @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ ( k6_subset_1 @ sk_A @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ ( k6_subset_1 @ sk_A @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('46',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X9 @ X10 )
      | ( r1_xboole_0 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    r1_xboole_0 @ sk_A @ ( k6_subset_1 @ sk_A @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('50',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k6_subset_1 @ X23 @ X24 )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('51',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k6_subset_1 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_xboole_0 @ X11 @ X12 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k6_subset_1 @ sk_A @ ( k6_subset_1 @ sk_A @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) )
    = sk_A ),
    inference('sup-',[status(thm)],['48','51'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('53',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('54',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k6_subset_1 @ X23 @ X24 )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('55',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k6_subset_1 @ X23 @ X24 )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('56',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k6_subset_1 @ X6 @ ( k6_subset_1 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['52','56'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('58',plain,(
    ! [X35: $i,X36: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X35 @ ( k10_relat_1 @ X35 @ X36 ) ) @ X36 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('59',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k6_subset_1 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k6_subset_1 @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k6_subset_1 @ X6 @ ( k6_subset_1 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_subset_1 @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) @ k1_xboole_0 )
        = ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X5: $i] :
      ( ( k6_subset_1 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X0 @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['57','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['69','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EN3hv4rIbV
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:33:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.69/0.91  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.69/0.91  % Solved by: fo/fo7.sh
% 0.69/0.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.91  % done 904 iterations in 0.462s
% 0.69/0.91  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.69/0.91  % SZS output start Refutation
% 0.69/0.91  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.69/0.91  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.69/0.91  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.69/0.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.69/0.91  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.69/0.91  thf(sk_B_type, type, sk_B: $i).
% 0.69/0.91  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.69/0.91  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.91  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.69/0.91  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.69/0.91  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.69/0.91  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.69/0.91  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.69/0.91  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.69/0.91  thf(t138_funct_1, axiom,
% 0.69/0.91    (![A:$i,B:$i,C:$i]:
% 0.69/0.91     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.69/0.91       ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 0.69/0.91         ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.69/0.91  thf('0', plain,
% 0.69/0.91      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.69/0.91         (((k10_relat_1 @ X32 @ (k6_subset_1 @ X33 @ X34))
% 0.69/0.91            = (k6_subset_1 @ (k10_relat_1 @ X32 @ X33) @ 
% 0.69/0.91               (k10_relat_1 @ X32 @ X34)))
% 0.69/0.91          | ~ (v1_funct_1 @ X32)
% 0.69/0.91          | ~ (v1_relat_1 @ X32))),
% 0.69/0.91      inference('cnf', [status(esa)], [t138_funct_1])).
% 0.69/0.91  thf(t169_relat_1, axiom,
% 0.69/0.91    (![A:$i]:
% 0.69/0.91     ( ( v1_relat_1 @ A ) =>
% 0.69/0.91       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.69/0.91  thf('1', plain,
% 0.69/0.91      (![X27 : $i]:
% 0.69/0.91         (((k10_relat_1 @ X27 @ (k2_relat_1 @ X27)) = (k1_relat_1 @ X27))
% 0.69/0.91          | ~ (v1_relat_1 @ X27))),
% 0.69/0.91      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.69/0.91  thf(t3_boole, axiom,
% 0.69/0.91    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.69/0.91  thf('2', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.69/0.91      inference('cnf', [status(esa)], [t3_boole])).
% 0.69/0.91  thf(redefinition_k6_subset_1, axiom,
% 0.69/0.91    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.69/0.91  thf('3', plain,
% 0.69/0.91      (![X23 : $i, X24 : $i]:
% 0.69/0.91         ((k6_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))),
% 0.69/0.91      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.69/0.91  thf('4', plain, (![X5 : $i]: ((k6_subset_1 @ X5 @ k1_xboole_0) = (X5))),
% 0.69/0.91      inference('demod', [status(thm)], ['2', '3'])).
% 0.69/0.91  thf(t83_xboole_1, axiom,
% 0.69/0.91    (![A:$i,B:$i]:
% 0.69/0.91     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.69/0.91  thf('5', plain,
% 0.69/0.91      (![X11 : $i, X13 : $i]:
% 0.69/0.91         ((r1_xboole_0 @ X11 @ X13) | ((k4_xboole_0 @ X11 @ X13) != (X11)))),
% 0.69/0.91      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.69/0.91  thf('6', plain,
% 0.69/0.91      (![X23 : $i, X24 : $i]:
% 0.69/0.91         ((k6_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))),
% 0.69/0.91      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.69/0.91  thf('7', plain,
% 0.69/0.91      (![X11 : $i, X13 : $i]:
% 0.69/0.91         ((r1_xboole_0 @ X11 @ X13) | ((k6_subset_1 @ X11 @ X13) != (X11)))),
% 0.69/0.91      inference('demod', [status(thm)], ['5', '6'])).
% 0.69/0.91  thf('8', plain,
% 0.69/0.91      (![X0 : $i]: (((X0) != (X0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.69/0.91      inference('sup-', [status(thm)], ['4', '7'])).
% 0.69/0.91  thf('9', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.69/0.91      inference('simplify', [status(thm)], ['8'])).
% 0.69/0.91  thf(t173_relat_1, axiom,
% 0.69/0.91    (![A:$i,B:$i]:
% 0.69/0.91     ( ( v1_relat_1 @ B ) =>
% 0.69/0.91       ( ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.69/0.91         ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.69/0.91  thf('10', plain,
% 0.69/0.91      (![X30 : $i, X31 : $i]:
% 0.69/0.91         (~ (r1_xboole_0 @ (k2_relat_1 @ X30) @ X31)
% 0.69/0.91          | ((k10_relat_1 @ X30 @ X31) = (k1_xboole_0))
% 0.69/0.91          | ~ (v1_relat_1 @ X30))),
% 0.69/0.91      inference('cnf', [status(esa)], [t173_relat_1])).
% 0.69/0.91  thf('11', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         (~ (v1_relat_1 @ X0)
% 0.69/0.91          | ((k10_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.69/0.91      inference('sup-', [status(thm)], ['9', '10'])).
% 0.69/0.91  thf(t147_funct_1, conjecture,
% 0.69/0.91    (![A:$i,B:$i]:
% 0.69/0.91     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.69/0.91       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.69/0.91         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.69/0.91  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.91    (~( ![A:$i,B:$i]:
% 0.69/0.91        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.69/0.91          ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.69/0.91            ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ) )),
% 0.69/0.91    inference('cnf.neg', [status(esa)], [t147_funct_1])).
% 0.69/0.91  thf('12', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf(l32_xboole_1, axiom,
% 0.69/0.91    (![A:$i,B:$i]:
% 0.69/0.91     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.69/0.91  thf('13', plain,
% 0.69/0.91      (![X2 : $i, X4 : $i]:
% 0.69/0.91         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.69/0.91      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.69/0.91  thf('14', plain,
% 0.69/0.91      (![X23 : $i, X24 : $i]:
% 0.69/0.91         ((k6_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))),
% 0.69/0.91      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.69/0.91  thf('15', plain,
% 0.69/0.91      (![X2 : $i, X4 : $i]:
% 0.69/0.91         (((k6_subset_1 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.69/0.91      inference('demod', [status(thm)], ['13', '14'])).
% 0.69/0.91  thf('16', plain,
% 0.69/0.91      (((k6_subset_1 @ sk_A @ (k2_relat_1 @ sk_B)) = (k1_xboole_0))),
% 0.69/0.91      inference('sup-', [status(thm)], ['12', '15'])).
% 0.69/0.91  thf('17', plain,
% 0.69/0.91      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.69/0.91         (((k10_relat_1 @ X32 @ (k6_subset_1 @ X33 @ X34))
% 0.69/0.91            = (k6_subset_1 @ (k10_relat_1 @ X32 @ X33) @ 
% 0.69/0.91               (k10_relat_1 @ X32 @ X34)))
% 0.69/0.91          | ~ (v1_funct_1 @ X32)
% 0.69/0.91          | ~ (v1_relat_1 @ X32))),
% 0.69/0.91      inference('cnf', [status(esa)], [t138_funct_1])).
% 0.69/0.91  thf('18', plain,
% 0.69/0.91      (![X2 : $i, X3 : $i]:
% 0.69/0.91         ((r1_tarski @ X2 @ X3) | ((k4_xboole_0 @ X2 @ X3) != (k1_xboole_0)))),
% 0.69/0.91      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.69/0.91  thf('19', plain,
% 0.69/0.91      (![X23 : $i, X24 : $i]:
% 0.69/0.91         ((k6_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))),
% 0.69/0.91      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.69/0.91  thf('20', plain,
% 0.69/0.91      (![X2 : $i, X3 : $i]:
% 0.69/0.91         ((r1_tarski @ X2 @ X3) | ((k6_subset_1 @ X2 @ X3) != (k1_xboole_0)))),
% 0.69/0.91      inference('demod', [status(thm)], ['18', '19'])).
% 0.69/0.91  thf('21', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.91         (((k10_relat_1 @ X2 @ (k6_subset_1 @ X1 @ X0)) != (k1_xboole_0))
% 0.69/0.91          | ~ (v1_relat_1 @ X2)
% 0.69/0.91          | ~ (v1_funct_1 @ X2)
% 0.69/0.91          | (r1_tarski @ (k10_relat_1 @ X2 @ X1) @ (k10_relat_1 @ X2 @ X0)))),
% 0.69/0.91      inference('sup-', [status(thm)], ['17', '20'])).
% 0.69/0.91  thf('22', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         (((k10_relat_1 @ X0 @ k1_xboole_0) != (k1_xboole_0))
% 0.69/0.91          | (r1_tarski @ (k10_relat_1 @ X0 @ sk_A) @ 
% 0.69/0.91             (k10_relat_1 @ X0 @ (k2_relat_1 @ sk_B)))
% 0.69/0.91          | ~ (v1_funct_1 @ X0)
% 0.69/0.91          | ~ (v1_relat_1 @ X0))),
% 0.69/0.91      inference('sup-', [status(thm)], ['16', '21'])).
% 0.69/0.91  thf('23', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         (((k1_xboole_0) != (k1_xboole_0))
% 0.69/0.91          | ~ (v1_relat_1 @ X0)
% 0.69/0.91          | ~ (v1_relat_1 @ X0)
% 0.69/0.91          | ~ (v1_funct_1 @ X0)
% 0.69/0.91          | (r1_tarski @ (k10_relat_1 @ X0 @ sk_A) @ 
% 0.69/0.91             (k10_relat_1 @ X0 @ (k2_relat_1 @ sk_B))))),
% 0.69/0.91      inference('sup-', [status(thm)], ['11', '22'])).
% 0.69/0.91  thf('24', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         ((r1_tarski @ (k10_relat_1 @ X0 @ sk_A) @ 
% 0.69/0.91           (k10_relat_1 @ X0 @ (k2_relat_1 @ sk_B)))
% 0.69/0.91          | ~ (v1_funct_1 @ X0)
% 0.69/0.91          | ~ (v1_relat_1 @ X0))),
% 0.69/0.91      inference('simplify', [status(thm)], ['23'])).
% 0.69/0.91  thf('25', plain,
% 0.69/0.91      (((r1_tarski @ (k10_relat_1 @ sk_B @ sk_A) @ (k1_relat_1 @ sk_B))
% 0.69/0.91        | ~ (v1_relat_1 @ sk_B)
% 0.69/0.91        | ~ (v1_relat_1 @ sk_B)
% 0.69/0.91        | ~ (v1_funct_1 @ sk_B))),
% 0.69/0.91      inference('sup+', [status(thm)], ['1', '24'])).
% 0.69/0.91  thf('26', plain, ((v1_relat_1 @ sk_B)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('27', plain, ((v1_relat_1 @ sk_B)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('28', plain, ((v1_funct_1 @ sk_B)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('29', plain,
% 0.69/0.91      ((r1_tarski @ (k10_relat_1 @ sk_B @ sk_A) @ (k1_relat_1 @ sk_B))),
% 0.69/0.91      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 0.69/0.91  thf(t146_funct_1, axiom,
% 0.69/0.91    (![A:$i,B:$i]:
% 0.69/0.91     ( ( v1_relat_1 @ B ) =>
% 0.69/0.91       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.69/0.91         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.69/0.91  thf('30', plain,
% 0.69/0.91      (![X37 : $i, X38 : $i]:
% 0.69/0.91         (~ (r1_tarski @ X37 @ (k1_relat_1 @ X38))
% 0.69/0.91          | (r1_tarski @ X37 @ (k10_relat_1 @ X38 @ (k9_relat_1 @ X38 @ X37)))
% 0.69/0.91          | ~ (v1_relat_1 @ X38))),
% 0.69/0.91      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.69/0.91  thf('31', plain,
% 0.69/0.91      ((~ (v1_relat_1 @ sk_B)
% 0.69/0.91        | (r1_tarski @ (k10_relat_1 @ sk_B @ sk_A) @ 
% 0.69/0.91           (k10_relat_1 @ sk_B @ 
% 0.69/0.91            (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)))))),
% 0.69/0.91      inference('sup-', [status(thm)], ['29', '30'])).
% 0.69/0.91  thf('32', plain, ((v1_relat_1 @ sk_B)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('33', plain,
% 0.69/0.91      ((r1_tarski @ (k10_relat_1 @ sk_B @ sk_A) @ 
% 0.69/0.91        (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))))),
% 0.69/0.91      inference('demod', [status(thm)], ['31', '32'])).
% 0.69/0.91  thf('34', plain,
% 0.69/0.91      (![X2 : $i, X4 : $i]:
% 0.69/0.91         (((k6_subset_1 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.69/0.91      inference('demod', [status(thm)], ['13', '14'])).
% 0.69/0.91  thf('35', plain,
% 0.69/0.91      (((k6_subset_1 @ (k10_relat_1 @ sk_B @ sk_A) @ 
% 0.69/0.91         (k10_relat_1 @ sk_B @ 
% 0.69/0.91          (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))))
% 0.69/0.91         = (k1_xboole_0))),
% 0.69/0.91      inference('sup-', [status(thm)], ['33', '34'])).
% 0.69/0.91  thf('36', plain,
% 0.69/0.91      ((((k10_relat_1 @ sk_B @ 
% 0.69/0.91          (k6_subset_1 @ sk_A @ 
% 0.69/0.91           (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))))
% 0.69/0.91          = (k1_xboole_0))
% 0.69/0.91        | ~ (v1_relat_1 @ sk_B)
% 0.69/0.91        | ~ (v1_funct_1 @ sk_B))),
% 0.69/0.91      inference('sup+', [status(thm)], ['0', '35'])).
% 0.69/0.91  thf('37', plain, ((v1_relat_1 @ sk_B)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('38', plain, ((v1_funct_1 @ sk_B)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('39', plain,
% 0.69/0.91      (((k10_relat_1 @ sk_B @ 
% 0.69/0.91         (k6_subset_1 @ sk_A @ 
% 0.69/0.91          (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))))
% 0.69/0.91         = (k1_xboole_0))),
% 0.69/0.91      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.69/0.91  thf('40', plain,
% 0.69/0.91      (![X30 : $i, X31 : $i]:
% 0.69/0.91         (((k10_relat_1 @ X30 @ X31) != (k1_xboole_0))
% 0.69/0.91          | (r1_xboole_0 @ (k2_relat_1 @ X30) @ X31)
% 0.69/0.91          | ~ (v1_relat_1 @ X30))),
% 0.69/0.91      inference('cnf', [status(esa)], [t173_relat_1])).
% 0.69/0.91  thf('41', plain,
% 0.69/0.91      ((((k1_xboole_0) != (k1_xboole_0))
% 0.69/0.91        | ~ (v1_relat_1 @ sk_B)
% 0.69/0.91        | (r1_xboole_0 @ (k2_relat_1 @ sk_B) @ 
% 0.69/0.91           (k6_subset_1 @ sk_A @ 
% 0.69/0.91            (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)))))),
% 0.69/0.91      inference('sup-', [status(thm)], ['39', '40'])).
% 0.69/0.91  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('43', plain,
% 0.69/0.91      ((((k1_xboole_0) != (k1_xboole_0))
% 0.69/0.91        | (r1_xboole_0 @ (k2_relat_1 @ sk_B) @ 
% 0.69/0.91           (k6_subset_1 @ sk_A @ 
% 0.69/0.91            (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)))))),
% 0.69/0.91      inference('demod', [status(thm)], ['41', '42'])).
% 0.69/0.91  thf('44', plain,
% 0.69/0.91      ((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ 
% 0.69/0.91        (k6_subset_1 @ sk_A @ (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))))),
% 0.69/0.91      inference('simplify', [status(thm)], ['43'])).
% 0.69/0.91  thf('45', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf(t63_xboole_1, axiom,
% 0.69/0.91    (![A:$i,B:$i,C:$i]:
% 0.69/0.91     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.69/0.91       ( r1_xboole_0 @ A @ C ) ))).
% 0.69/0.91  thf('46', plain,
% 0.69/0.91      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.69/0.91         (~ (r1_tarski @ X8 @ X9)
% 0.69/0.91          | ~ (r1_xboole_0 @ X9 @ X10)
% 0.69/0.91          | (r1_xboole_0 @ X8 @ X10))),
% 0.69/0.91      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.69/0.91  thf('47', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         ((r1_xboole_0 @ sk_A @ X0)
% 0.69/0.91          | ~ (r1_xboole_0 @ (k2_relat_1 @ sk_B) @ X0))),
% 0.69/0.91      inference('sup-', [status(thm)], ['45', '46'])).
% 0.69/0.91  thf('48', plain,
% 0.69/0.91      ((r1_xboole_0 @ sk_A @ 
% 0.69/0.91        (k6_subset_1 @ sk_A @ (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))))),
% 0.69/0.91      inference('sup-', [status(thm)], ['44', '47'])).
% 0.69/0.91  thf('49', plain,
% 0.69/0.91      (![X11 : $i, X12 : $i]:
% 0.69/0.91         (((k4_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_xboole_0 @ X11 @ X12))),
% 0.69/0.91      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.69/0.91  thf('50', plain,
% 0.69/0.91      (![X23 : $i, X24 : $i]:
% 0.69/0.91         ((k6_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))),
% 0.69/0.91      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.69/0.91  thf('51', plain,
% 0.69/0.91      (![X11 : $i, X12 : $i]:
% 0.69/0.91         (((k6_subset_1 @ X11 @ X12) = (X11)) | ~ (r1_xboole_0 @ X11 @ X12))),
% 0.69/0.91      inference('demod', [status(thm)], ['49', '50'])).
% 0.69/0.91  thf('52', plain,
% 0.69/0.91      (((k6_subset_1 @ sk_A @ 
% 0.69/0.91         (k6_subset_1 @ sk_A @ 
% 0.69/0.91          (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))))
% 0.69/0.91         = (sk_A))),
% 0.69/0.91      inference('sup-', [status(thm)], ['48', '51'])).
% 0.69/0.91  thf(t48_xboole_1, axiom,
% 0.69/0.91    (![A:$i,B:$i]:
% 0.69/0.91     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.69/0.91  thf('53', plain,
% 0.69/0.91      (![X6 : $i, X7 : $i]:
% 0.69/0.91         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.69/0.91           = (k3_xboole_0 @ X6 @ X7))),
% 0.69/0.91      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.69/0.91  thf('54', plain,
% 0.69/0.91      (![X23 : $i, X24 : $i]:
% 0.69/0.91         ((k6_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))),
% 0.69/0.91      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.69/0.91  thf('55', plain,
% 0.69/0.91      (![X23 : $i, X24 : $i]:
% 0.69/0.91         ((k6_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))),
% 0.69/0.91      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.69/0.91  thf('56', plain,
% 0.69/0.91      (![X6 : $i, X7 : $i]:
% 0.69/0.91         ((k6_subset_1 @ X6 @ (k6_subset_1 @ X6 @ X7))
% 0.69/0.91           = (k3_xboole_0 @ X6 @ X7))),
% 0.69/0.91      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.69/0.91  thf('57', plain,
% 0.69/0.91      (((k3_xboole_0 @ sk_A @ (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)))
% 0.69/0.91         = (sk_A))),
% 0.69/0.91      inference('demod', [status(thm)], ['52', '56'])).
% 0.69/0.91  thf(t145_funct_1, axiom,
% 0.69/0.91    (![A:$i,B:$i]:
% 0.69/0.91     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.69/0.91       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 0.69/0.91  thf('58', plain,
% 0.69/0.91      (![X35 : $i, X36 : $i]:
% 0.69/0.91         ((r1_tarski @ (k9_relat_1 @ X35 @ (k10_relat_1 @ X35 @ X36)) @ X36)
% 0.69/0.91          | ~ (v1_funct_1 @ X35)
% 0.69/0.91          | ~ (v1_relat_1 @ X35))),
% 0.69/0.91      inference('cnf', [status(esa)], [t145_funct_1])).
% 0.69/0.91  thf('59', plain,
% 0.69/0.91      (![X2 : $i, X4 : $i]:
% 0.69/0.91         (((k6_subset_1 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.69/0.91      inference('demod', [status(thm)], ['13', '14'])).
% 0.69/0.91  thf('60', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i]:
% 0.69/0.91         (~ (v1_relat_1 @ X1)
% 0.69/0.91          | ~ (v1_funct_1 @ X1)
% 0.69/0.91          | ((k6_subset_1 @ (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0)) @ X0)
% 0.69/0.91              = (k1_xboole_0)))),
% 0.69/0.91      inference('sup-', [status(thm)], ['58', '59'])).
% 0.69/0.91  thf('61', plain,
% 0.69/0.91      (![X6 : $i, X7 : $i]:
% 0.69/0.91         ((k6_subset_1 @ X6 @ (k6_subset_1 @ X6 @ X7))
% 0.69/0.91           = (k3_xboole_0 @ X6 @ X7))),
% 0.69/0.91      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.69/0.91  thf('62', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i]:
% 0.69/0.91         (((k6_subset_1 @ (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0)) @ 
% 0.69/0.91            k1_xboole_0)
% 0.69/0.91            = (k3_xboole_0 @ (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0)) @ X0))
% 0.69/0.91          | ~ (v1_funct_1 @ X1)
% 0.69/0.91          | ~ (v1_relat_1 @ X1))),
% 0.69/0.91      inference('sup+', [status(thm)], ['60', '61'])).
% 0.69/0.91  thf('63', plain, (![X5 : $i]: ((k6_subset_1 @ X5 @ k1_xboole_0) = (X5))),
% 0.69/0.91      inference('demod', [status(thm)], ['2', '3'])).
% 0.69/0.91  thf(commutativity_k3_xboole_0, axiom,
% 0.69/0.91    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.69/0.91  thf('64', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.69/0.91      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.69/0.91  thf('65', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i]:
% 0.69/0.91         (((k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0))
% 0.69/0.91            = (k3_xboole_0 @ X0 @ (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0))))
% 0.69/0.91          | ~ (v1_funct_1 @ X1)
% 0.69/0.91          | ~ (v1_relat_1 @ X1))),
% 0.69/0.91      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.69/0.91  thf('66', plain,
% 0.69/0.91      ((((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)) = (sk_A))
% 0.69/0.91        | ~ (v1_relat_1 @ sk_B)
% 0.69/0.91        | ~ (v1_funct_1 @ sk_B))),
% 0.69/0.91      inference('sup+', [status(thm)], ['57', '65'])).
% 0.69/0.91  thf('67', plain, ((v1_relat_1 @ sk_B)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('68', plain, ((v1_funct_1 @ sk_B)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('69', plain,
% 0.69/0.91      (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 0.69/0.91      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.69/0.91  thf('70', plain,
% 0.69/0.91      (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)) != (sk_A))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('71', plain, ($false),
% 0.69/0.91      inference('simplify_reflect-', [status(thm)], ['69', '70'])).
% 0.69/0.91  
% 0.69/0.91  % SZS output end Refutation
% 0.69/0.91  
% 0.69/0.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
