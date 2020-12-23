%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6CbGIzioJP

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:29 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 160 expanded)
%              Number of leaves         :   23 (  56 expanded)
%              Depth                    :   24
%              Number of atoms          :  746 (1404 expanded)
%              Number of equality atoms :   60 ( 120 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t138_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('0',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k10_relat_1 @ X25 @ ( k6_subset_1 @ X26 @ X27 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X25 @ X26 ) @ ( k10_relat_1 @ X25 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('6',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k6_subset_1 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k10_relat_1 @ X25 @ ( k6_subset_1 @ X26 @ X27 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X25 @ X26 ) @ ( k10_relat_1 @ X25 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('12',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X11 @ X12 ) @ X11 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k6_subset_1 @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k10_relat_1 @ X1 @ ( k6_subset_1 @ X0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','17'])).

thf('19',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k10_relat_1 @ X1 @ k1_xboole_0 ) )
      | ( X2 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','19'])).

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

thf('21',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k6_subset_1 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('23',plain,
    ( ( k6_subset_1 @ sk_A @ ( k2_relat_1 @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('24',plain,(
    ! [X22: $i] :
      ( ( ( k10_relat_1 @ X22 @ ( k2_relat_1 @ X22 ) )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('25',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k10_relat_1 @ X25 @ ( k6_subset_1 @ X26 @ X27 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X25 @ X26 ) @ ( k10_relat_1 @ X25 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k6_subset_1 @ X1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k6_subset_1 @ X1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( ( k10_relat_1 @ sk_B @ k1_xboole_0 )
      = ( k6_subset_1 @ ( k10_relat_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['23','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k10_relat_1 @ sk_B @ k1_xboole_0 )
    = ( k6_subset_1 @ ( k10_relat_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('33',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('34',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k6_subset_1 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k10_relat_1 @ sk_B @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( r1_tarski @ ( k10_relat_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ ( k10_relat_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k10_relat_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['39'])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('41',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ X30 @ ( k1_relat_1 @ X31 ) )
      | ( r1_tarski @ X30 @ ( k10_relat_1 @ X31 @ ( k9_relat_1 @ X31 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ ( k10_relat_1 @ sk_B @ sk_A ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_B @ sk_A ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k6_subset_1 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('46',plain,
    ( ( k6_subset_1 @ ( k10_relat_1 @ sk_B @ sk_A ) @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k6_subset_1 @ sk_A @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k10_relat_1 @ sk_B @ ( k6_subset_1 @ sk_A @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t109_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('52',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ ( k4_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('53',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('54',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ ( k6_subset_1 @ X8 @ X10 ) @ X9 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_A @ X0 ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf(t174_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( A != k1_xboole_0 )
          & ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
          & ( ( k10_relat_1 @ B @ A )
            = k1_xboole_0 ) ) ) )).

thf('56',plain,(
    ! [X23: $i,X24: $i] :
      ( ( X23 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X24 )
      | ~ ( r1_tarski @ X23 @ ( k2_relat_1 @ X24 ) )
      | ( ( k10_relat_1 @ X24 @ X23 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t174_relat_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_B @ ( k6_subset_1 @ sk_A @ X0 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( ( k6_subset_1 @ sk_A @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_B @ ( k6_subset_1 @ sk_A @ X0 ) )
       != k1_xboole_0 )
      | ( ( k6_subset_1 @ sk_A @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k6_subset_1 @ sk_A @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','59'])).

thf('61',plain,
    ( ( k6_subset_1 @ sk_A @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k6_subset_1 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('63',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    r1_tarski @ sk_A @ ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('65',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X28 @ ( k10_relat_1 @ X28 @ X29 ) ) @ X29 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('66',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( sk_A
      = ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( sk_A
    = ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['71','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6CbGIzioJP
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:02:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.61/1.79  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.61/1.79  % Solved by: fo/fo7.sh
% 1.61/1.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.61/1.79  % done 3632 iterations in 1.340s
% 1.61/1.79  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.61/1.79  % SZS output start Refutation
% 1.61/1.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.61/1.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.61/1.79  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.61/1.79  thf(sk_A_type, type, sk_A: $i).
% 1.61/1.79  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.61/1.79  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.61/1.79  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.61/1.79  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 1.61/1.79  thf(sk_B_type, type, sk_B: $i).
% 1.61/1.79  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.61/1.79  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.61/1.79  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.61/1.79  thf(t138_funct_1, axiom,
% 1.61/1.79    (![A:$i,B:$i,C:$i]:
% 1.61/1.79     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.61/1.79       ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 1.61/1.79         ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 1.61/1.79  thf('0', plain,
% 1.61/1.79      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.61/1.79         (((k10_relat_1 @ X25 @ (k6_subset_1 @ X26 @ X27))
% 1.61/1.79            = (k6_subset_1 @ (k10_relat_1 @ X25 @ X26) @ 
% 1.61/1.79               (k10_relat_1 @ X25 @ X27)))
% 1.61/1.79          | ~ (v1_funct_1 @ X25)
% 1.61/1.79          | ~ (v1_relat_1 @ X25))),
% 1.61/1.79      inference('cnf', [status(esa)], [t138_funct_1])).
% 1.61/1.79  thf(d10_xboole_0, axiom,
% 1.61/1.79    (![A:$i,B:$i]:
% 1.61/1.79     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.61/1.79  thf('1', plain,
% 1.61/1.79      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 1.61/1.79      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.61/1.79  thf('2', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 1.61/1.79      inference('simplify', [status(thm)], ['1'])).
% 1.61/1.79  thf('3', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 1.61/1.79      inference('simplify', [status(thm)], ['1'])).
% 1.61/1.79  thf(l32_xboole_1, axiom,
% 1.61/1.79    (![A:$i,B:$i]:
% 1.61/1.79     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.61/1.79  thf('4', plain,
% 1.61/1.79      (![X5 : $i, X7 : $i]:
% 1.61/1.79         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 1.61/1.79      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.61/1.79  thf(redefinition_k6_subset_1, axiom,
% 1.61/1.79    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.61/1.79  thf('5', plain,
% 1.61/1.79      (![X18 : $i, X19 : $i]:
% 1.61/1.79         ((k6_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))),
% 1.61/1.79      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.61/1.79  thf('6', plain,
% 1.61/1.79      (![X5 : $i, X7 : $i]:
% 1.61/1.79         (((k6_subset_1 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 1.61/1.79      inference('demod', [status(thm)], ['4', '5'])).
% 1.61/1.79  thf('7', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 1.61/1.79      inference('sup-', [status(thm)], ['3', '6'])).
% 1.61/1.79  thf('8', plain,
% 1.61/1.79      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.61/1.79         (((k10_relat_1 @ X25 @ (k6_subset_1 @ X26 @ X27))
% 1.61/1.79            = (k6_subset_1 @ (k10_relat_1 @ X25 @ X26) @ 
% 1.61/1.79               (k10_relat_1 @ X25 @ X27)))
% 1.61/1.79          | ~ (v1_funct_1 @ X25)
% 1.61/1.79          | ~ (v1_relat_1 @ X25))),
% 1.61/1.79      inference('cnf', [status(esa)], [t138_funct_1])).
% 1.61/1.79  thf('9', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 1.61/1.79      inference('sup-', [status(thm)], ['3', '6'])).
% 1.61/1.79  thf('10', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 1.61/1.79      inference('sup-', [status(thm)], ['3', '6'])).
% 1.61/1.79  thf(t36_xboole_1, axiom,
% 1.61/1.79    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.61/1.79  thf('11', plain,
% 1.61/1.79      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 1.61/1.79      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.61/1.79  thf('12', plain,
% 1.61/1.79      (![X18 : $i, X19 : $i]:
% 1.61/1.79         ((k6_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))),
% 1.61/1.79      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.61/1.79  thf('13', plain,
% 1.61/1.79      (![X11 : $i, X12 : $i]: (r1_tarski @ (k6_subset_1 @ X11 @ X12) @ X11)),
% 1.61/1.79      inference('demod', [status(thm)], ['11', '12'])).
% 1.61/1.79  thf('14', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.61/1.79      inference('sup+', [status(thm)], ['10', '13'])).
% 1.61/1.79  thf('15', plain,
% 1.61/1.79      (![X2 : $i, X4 : $i]:
% 1.61/1.79         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 1.61/1.79      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.61/1.79  thf('16', plain,
% 1.61/1.79      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.61/1.79      inference('sup-', [status(thm)], ['14', '15'])).
% 1.61/1.79  thf('17', plain,
% 1.61/1.79      (![X0 : $i, X1 : $i]:
% 1.61/1.79         (~ (r1_tarski @ X1 @ (k6_subset_1 @ X0 @ X0)) | ((X1) = (k1_xboole_0)))),
% 1.61/1.79      inference('sup-', [status(thm)], ['9', '16'])).
% 1.61/1.79  thf('18', plain,
% 1.61/1.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.61/1.79         (~ (r1_tarski @ X2 @ (k10_relat_1 @ X1 @ (k6_subset_1 @ X0 @ X0)))
% 1.61/1.79          | ~ (v1_relat_1 @ X1)
% 1.61/1.79          | ~ (v1_funct_1 @ X1)
% 1.61/1.79          | ((X2) = (k1_xboole_0)))),
% 1.61/1.79      inference('sup-', [status(thm)], ['8', '17'])).
% 1.61/1.79  thf('19', plain,
% 1.61/1.79      (![X1 : $i, X2 : $i]:
% 1.61/1.79         (~ (r1_tarski @ X2 @ (k10_relat_1 @ X1 @ k1_xboole_0))
% 1.61/1.79          | ((X2) = (k1_xboole_0))
% 1.61/1.79          | ~ (v1_funct_1 @ X1)
% 1.61/1.79          | ~ (v1_relat_1 @ X1))),
% 1.61/1.79      inference('sup-', [status(thm)], ['7', '18'])).
% 1.61/1.79  thf('20', plain,
% 1.61/1.79      (![X0 : $i]:
% 1.61/1.79         (~ (v1_relat_1 @ X0)
% 1.61/1.79          | ~ (v1_funct_1 @ X0)
% 1.61/1.79          | ((k10_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 1.61/1.79      inference('sup-', [status(thm)], ['2', '19'])).
% 1.61/1.79  thf(t147_funct_1, conjecture,
% 1.61/1.79    (![A:$i,B:$i]:
% 1.61/1.79     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.61/1.79       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 1.61/1.79         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 1.61/1.79  thf(zf_stmt_0, negated_conjecture,
% 1.61/1.79    (~( ![A:$i,B:$i]:
% 1.61/1.79        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.61/1.79          ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 1.61/1.79            ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ) )),
% 1.61/1.79    inference('cnf.neg', [status(esa)], [t147_funct_1])).
% 1.61/1.79  thf('21', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))),
% 1.61/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.79  thf('22', plain,
% 1.61/1.79      (![X5 : $i, X7 : $i]:
% 1.61/1.79         (((k6_subset_1 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 1.61/1.79      inference('demod', [status(thm)], ['4', '5'])).
% 1.61/1.79  thf('23', plain,
% 1.61/1.79      (((k6_subset_1 @ sk_A @ (k2_relat_1 @ sk_B)) = (k1_xboole_0))),
% 1.61/1.79      inference('sup-', [status(thm)], ['21', '22'])).
% 1.61/1.79  thf(t169_relat_1, axiom,
% 1.61/1.79    (![A:$i]:
% 1.61/1.79     ( ( v1_relat_1 @ A ) =>
% 1.61/1.79       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 1.61/1.79  thf('24', plain,
% 1.61/1.79      (![X22 : $i]:
% 1.61/1.79         (((k10_relat_1 @ X22 @ (k2_relat_1 @ X22)) = (k1_relat_1 @ X22))
% 1.61/1.79          | ~ (v1_relat_1 @ X22))),
% 1.61/1.79      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.61/1.79  thf('25', plain,
% 1.61/1.79      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.61/1.79         (((k10_relat_1 @ X25 @ (k6_subset_1 @ X26 @ X27))
% 1.61/1.79            = (k6_subset_1 @ (k10_relat_1 @ X25 @ X26) @ 
% 1.61/1.79               (k10_relat_1 @ X25 @ X27)))
% 1.61/1.79          | ~ (v1_funct_1 @ X25)
% 1.61/1.79          | ~ (v1_relat_1 @ X25))),
% 1.61/1.79      inference('cnf', [status(esa)], [t138_funct_1])).
% 1.61/1.79  thf('26', plain,
% 1.61/1.79      (![X0 : $i, X1 : $i]:
% 1.61/1.79         (((k10_relat_1 @ X0 @ (k6_subset_1 @ X1 @ (k2_relat_1 @ X0)))
% 1.61/1.79            = (k6_subset_1 @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0)))
% 1.61/1.79          | ~ (v1_relat_1 @ X0)
% 1.61/1.79          | ~ (v1_relat_1 @ X0)
% 1.61/1.79          | ~ (v1_funct_1 @ X0))),
% 1.61/1.79      inference('sup+', [status(thm)], ['24', '25'])).
% 1.61/1.79  thf('27', plain,
% 1.61/1.79      (![X0 : $i, X1 : $i]:
% 1.61/1.79         (~ (v1_funct_1 @ X0)
% 1.61/1.79          | ~ (v1_relat_1 @ X0)
% 1.61/1.79          | ((k10_relat_1 @ X0 @ (k6_subset_1 @ X1 @ (k2_relat_1 @ X0)))
% 1.61/1.79              = (k6_subset_1 @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))))),
% 1.61/1.79      inference('simplify', [status(thm)], ['26'])).
% 1.61/1.79  thf('28', plain,
% 1.61/1.79      ((((k10_relat_1 @ sk_B @ k1_xboole_0)
% 1.61/1.79          = (k6_subset_1 @ (k10_relat_1 @ sk_B @ sk_A) @ (k1_relat_1 @ sk_B)))
% 1.61/1.79        | ~ (v1_relat_1 @ sk_B)
% 1.61/1.79        | ~ (v1_funct_1 @ sk_B))),
% 1.61/1.79      inference('sup+', [status(thm)], ['23', '27'])).
% 1.61/1.79  thf('29', plain, ((v1_relat_1 @ sk_B)),
% 1.61/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.79  thf('30', plain, ((v1_funct_1 @ sk_B)),
% 1.61/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.79  thf('31', plain,
% 1.61/1.79      (((k10_relat_1 @ sk_B @ k1_xboole_0)
% 1.61/1.79         = (k6_subset_1 @ (k10_relat_1 @ sk_B @ sk_A) @ (k1_relat_1 @ sk_B)))),
% 1.61/1.79      inference('demod', [status(thm)], ['28', '29', '30'])).
% 1.61/1.79  thf('32', plain,
% 1.61/1.79      (![X5 : $i, X6 : $i]:
% 1.61/1.79         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 1.61/1.79      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.61/1.79  thf('33', plain,
% 1.61/1.79      (![X18 : $i, X19 : $i]:
% 1.61/1.79         ((k6_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))),
% 1.61/1.79      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.61/1.79  thf('34', plain,
% 1.61/1.79      (![X5 : $i, X6 : $i]:
% 1.61/1.79         ((r1_tarski @ X5 @ X6) | ((k6_subset_1 @ X5 @ X6) != (k1_xboole_0)))),
% 1.61/1.79      inference('demod', [status(thm)], ['32', '33'])).
% 1.61/1.79  thf('35', plain,
% 1.61/1.79      ((((k10_relat_1 @ sk_B @ k1_xboole_0) != (k1_xboole_0))
% 1.61/1.79        | (r1_tarski @ (k10_relat_1 @ sk_B @ sk_A) @ (k1_relat_1 @ sk_B)))),
% 1.61/1.79      inference('sup-', [status(thm)], ['31', '34'])).
% 1.61/1.79  thf('36', plain,
% 1.61/1.79      ((((k1_xboole_0) != (k1_xboole_0))
% 1.61/1.79        | ~ (v1_funct_1 @ sk_B)
% 1.61/1.79        | ~ (v1_relat_1 @ sk_B)
% 1.61/1.79        | (r1_tarski @ (k10_relat_1 @ sk_B @ sk_A) @ (k1_relat_1 @ sk_B)))),
% 1.61/1.79      inference('sup-', [status(thm)], ['20', '35'])).
% 1.61/1.79  thf('37', plain, ((v1_funct_1 @ sk_B)),
% 1.61/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.79  thf('38', plain, ((v1_relat_1 @ sk_B)),
% 1.61/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.79  thf('39', plain,
% 1.61/1.79      ((((k1_xboole_0) != (k1_xboole_0))
% 1.61/1.79        | (r1_tarski @ (k10_relat_1 @ sk_B @ sk_A) @ (k1_relat_1 @ sk_B)))),
% 1.61/1.79      inference('demod', [status(thm)], ['36', '37', '38'])).
% 1.61/1.79  thf('40', plain,
% 1.61/1.79      ((r1_tarski @ (k10_relat_1 @ sk_B @ sk_A) @ (k1_relat_1 @ sk_B))),
% 1.61/1.79      inference('simplify', [status(thm)], ['39'])).
% 1.61/1.79  thf(t146_funct_1, axiom,
% 1.61/1.79    (![A:$i,B:$i]:
% 1.61/1.79     ( ( v1_relat_1 @ B ) =>
% 1.61/1.79       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 1.61/1.79         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 1.61/1.79  thf('41', plain,
% 1.61/1.79      (![X30 : $i, X31 : $i]:
% 1.61/1.79         (~ (r1_tarski @ X30 @ (k1_relat_1 @ X31))
% 1.61/1.79          | (r1_tarski @ X30 @ (k10_relat_1 @ X31 @ (k9_relat_1 @ X31 @ X30)))
% 1.61/1.79          | ~ (v1_relat_1 @ X31))),
% 1.61/1.79      inference('cnf', [status(esa)], [t146_funct_1])).
% 1.61/1.79  thf('42', plain,
% 1.61/1.79      ((~ (v1_relat_1 @ sk_B)
% 1.61/1.79        | (r1_tarski @ (k10_relat_1 @ sk_B @ sk_A) @ 
% 1.61/1.79           (k10_relat_1 @ sk_B @ 
% 1.61/1.79            (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)))))),
% 1.61/1.80      inference('sup-', [status(thm)], ['40', '41'])).
% 1.61/1.80  thf('43', plain, ((v1_relat_1 @ sk_B)),
% 1.61/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.80  thf('44', plain,
% 1.61/1.80      ((r1_tarski @ (k10_relat_1 @ sk_B @ sk_A) @ 
% 1.61/1.80        (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))))),
% 1.61/1.80      inference('demod', [status(thm)], ['42', '43'])).
% 1.61/1.80  thf('45', plain,
% 1.61/1.80      (![X5 : $i, X7 : $i]:
% 1.61/1.80         (((k6_subset_1 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 1.61/1.80      inference('demod', [status(thm)], ['4', '5'])).
% 1.61/1.80  thf('46', plain,
% 1.61/1.80      (((k6_subset_1 @ (k10_relat_1 @ sk_B @ sk_A) @ 
% 1.61/1.80         (k10_relat_1 @ sk_B @ 
% 1.61/1.80          (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))))
% 1.61/1.80         = (k1_xboole_0))),
% 1.61/1.80      inference('sup-', [status(thm)], ['44', '45'])).
% 1.61/1.80  thf('47', plain,
% 1.61/1.80      ((((k10_relat_1 @ sk_B @ 
% 1.61/1.80          (k6_subset_1 @ sk_A @ 
% 1.61/1.80           (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))))
% 1.61/1.80          = (k1_xboole_0))
% 1.61/1.80        | ~ (v1_relat_1 @ sk_B)
% 1.61/1.80        | ~ (v1_funct_1 @ sk_B))),
% 1.61/1.80      inference('sup+', [status(thm)], ['0', '46'])).
% 1.61/1.80  thf('48', plain, ((v1_relat_1 @ sk_B)),
% 1.61/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.80  thf('49', plain, ((v1_funct_1 @ sk_B)),
% 1.61/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.80  thf('50', plain,
% 1.61/1.80      (((k10_relat_1 @ sk_B @ 
% 1.61/1.80         (k6_subset_1 @ sk_A @ 
% 1.61/1.80          (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))))
% 1.61/1.80         = (k1_xboole_0))),
% 1.61/1.80      inference('demod', [status(thm)], ['47', '48', '49'])).
% 1.61/1.80  thf('51', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))),
% 1.61/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.80  thf(t109_xboole_1, axiom,
% 1.61/1.80    (![A:$i,B:$i,C:$i]:
% 1.61/1.80     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 1.61/1.80  thf('52', plain,
% 1.61/1.80      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.61/1.80         (~ (r1_tarski @ X8 @ X9) | (r1_tarski @ (k4_xboole_0 @ X8 @ X10) @ X9))),
% 1.61/1.80      inference('cnf', [status(esa)], [t109_xboole_1])).
% 1.61/1.80  thf('53', plain,
% 1.61/1.80      (![X18 : $i, X19 : $i]:
% 1.61/1.80         ((k6_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))),
% 1.61/1.80      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.61/1.80  thf('54', plain,
% 1.61/1.80      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.61/1.80         (~ (r1_tarski @ X8 @ X9) | (r1_tarski @ (k6_subset_1 @ X8 @ X10) @ X9))),
% 1.61/1.80      inference('demod', [status(thm)], ['52', '53'])).
% 1.61/1.80  thf('55', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         (r1_tarski @ (k6_subset_1 @ sk_A @ X0) @ (k2_relat_1 @ sk_B))),
% 1.61/1.80      inference('sup-', [status(thm)], ['51', '54'])).
% 1.61/1.80  thf(t174_relat_1, axiom,
% 1.61/1.80    (![A:$i,B:$i]:
% 1.61/1.80     ( ( v1_relat_1 @ B ) =>
% 1.61/1.80       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.61/1.80            ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) & 
% 1.61/1.80            ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 1.61/1.80  thf('56', plain,
% 1.61/1.80      (![X23 : $i, X24 : $i]:
% 1.61/1.80         (((X23) = (k1_xboole_0))
% 1.61/1.80          | ~ (v1_relat_1 @ X24)
% 1.61/1.80          | ~ (r1_tarski @ X23 @ (k2_relat_1 @ X24))
% 1.61/1.80          | ((k10_relat_1 @ X24 @ X23) != (k1_xboole_0)))),
% 1.61/1.80      inference('cnf', [status(esa)], [t174_relat_1])).
% 1.61/1.80  thf('57', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         (((k10_relat_1 @ sk_B @ (k6_subset_1 @ sk_A @ X0)) != (k1_xboole_0))
% 1.61/1.80          | ~ (v1_relat_1 @ sk_B)
% 1.61/1.80          | ((k6_subset_1 @ sk_A @ X0) = (k1_xboole_0)))),
% 1.61/1.80      inference('sup-', [status(thm)], ['55', '56'])).
% 1.61/1.80  thf('58', plain, ((v1_relat_1 @ sk_B)),
% 1.61/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.80  thf('59', plain,
% 1.61/1.80      (![X0 : $i]:
% 1.61/1.80         (((k10_relat_1 @ sk_B @ (k6_subset_1 @ sk_A @ X0)) != (k1_xboole_0))
% 1.61/1.80          | ((k6_subset_1 @ sk_A @ X0) = (k1_xboole_0)))),
% 1.61/1.80      inference('demod', [status(thm)], ['57', '58'])).
% 1.61/1.80  thf('60', plain,
% 1.61/1.80      ((((k1_xboole_0) != (k1_xboole_0))
% 1.61/1.80        | ((k6_subset_1 @ sk_A @ 
% 1.61/1.80            (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))) = (k1_xboole_0)))),
% 1.61/1.80      inference('sup-', [status(thm)], ['50', '59'])).
% 1.61/1.80  thf('61', plain,
% 1.61/1.80      (((k6_subset_1 @ sk_A @ (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)))
% 1.61/1.80         = (k1_xboole_0))),
% 1.61/1.80      inference('simplify', [status(thm)], ['60'])).
% 1.61/1.80  thf('62', plain,
% 1.61/1.80      (![X5 : $i, X6 : $i]:
% 1.61/1.80         ((r1_tarski @ X5 @ X6) | ((k6_subset_1 @ X5 @ X6) != (k1_xboole_0)))),
% 1.61/1.80      inference('demod', [status(thm)], ['32', '33'])).
% 1.61/1.80  thf('63', plain,
% 1.61/1.80      ((((k1_xboole_0) != (k1_xboole_0))
% 1.61/1.80        | (r1_tarski @ sk_A @ (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))))),
% 1.61/1.80      inference('sup-', [status(thm)], ['61', '62'])).
% 1.61/1.80  thf('64', plain,
% 1.61/1.80      ((r1_tarski @ sk_A @ (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)))),
% 1.61/1.80      inference('simplify', [status(thm)], ['63'])).
% 1.61/1.80  thf(t145_funct_1, axiom,
% 1.61/1.80    (![A:$i,B:$i]:
% 1.61/1.80     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.61/1.80       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 1.61/1.80  thf('65', plain,
% 1.61/1.80      (![X28 : $i, X29 : $i]:
% 1.61/1.80         ((r1_tarski @ (k9_relat_1 @ X28 @ (k10_relat_1 @ X28 @ X29)) @ X29)
% 1.61/1.80          | ~ (v1_funct_1 @ X28)
% 1.61/1.80          | ~ (v1_relat_1 @ X28))),
% 1.61/1.80      inference('cnf', [status(esa)], [t145_funct_1])).
% 1.61/1.80  thf('66', plain,
% 1.61/1.80      (![X2 : $i, X4 : $i]:
% 1.61/1.80         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 1.61/1.80      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.61/1.80  thf('67', plain,
% 1.61/1.80      (![X0 : $i, X1 : $i]:
% 1.61/1.80         (~ (v1_relat_1 @ X1)
% 1.61/1.80          | ~ (v1_funct_1 @ X1)
% 1.61/1.80          | ~ (r1_tarski @ X0 @ (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0)))
% 1.61/1.80          | ((X0) = (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0))))),
% 1.61/1.80      inference('sup-', [status(thm)], ['65', '66'])).
% 1.61/1.80  thf('68', plain,
% 1.61/1.80      ((((sk_A) = (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)))
% 1.61/1.80        | ~ (v1_funct_1 @ sk_B)
% 1.61/1.80        | ~ (v1_relat_1 @ sk_B))),
% 1.61/1.80      inference('sup-', [status(thm)], ['64', '67'])).
% 1.61/1.80  thf('69', plain, ((v1_funct_1 @ sk_B)),
% 1.61/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.80  thf('70', plain, ((v1_relat_1 @ sk_B)),
% 1.61/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.80  thf('71', plain,
% 1.61/1.80      (((sk_A) = (k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)))),
% 1.61/1.80      inference('demod', [status(thm)], ['68', '69', '70'])).
% 1.61/1.80  thf('72', plain,
% 1.61/1.80      (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A)) != (sk_A))),
% 1.61/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.80  thf('73', plain, ($false),
% 1.61/1.80      inference('simplify_reflect-', [status(thm)], ['71', '72'])).
% 1.61/1.80  
% 1.61/1.80  % SZS output end Refutation
% 1.61/1.80  
% 1.61/1.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
